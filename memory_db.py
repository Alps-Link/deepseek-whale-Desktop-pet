# -*- coding: utf-8 -*-
"""SQLite 记忆存储层，用于阿尔卑斯桌宠的记忆系统。"""

import os
import sqlite3
import json
import threading
import uuid
from datetime import datetime

import numpy as np


class MemoryDB:
    """基于 SQLite 的记忆存储，当前以整表替换方式与内存 dict 同步。"""

    def __init__(self, db_path):
        self.db_path = db_path
        self._conn = None
        self._lock = threading.Lock()

    def connect(self):
        if self._conn is None:
            os.makedirs(os.path.dirname(self.db_path), exist_ok=True)
            self._conn = sqlite3.connect(self.db_path, check_same_thread=False)
            self._conn.row_factory = sqlite3.Row
            self._init_table()
        return self._conn

    def close(self):
        if self._conn is not None:
            self._conn.close()
            self._conn = None

    def _init_table(self):
        conn = self.connect()
        conn.execute("""
            CREATE TABLE IF NOT EXISTS memories (
                id TEXT PRIMARY KEY,
                type TEXT,
                content TEXT,
                embedding BLOB,
                importance REAL,
                access_count INTEGER,
                last_accessed_at TEXT,
                evidence_count INTEGER,
                archived INTEGER,
                archived_at TEXT,
                source TEXT,
                created_at TEXT,
                observation TEXT,
                description TEXT,
                evidence TEXT
            )
        """)
        # 兼容旧库：缺列时补列（性格画像的观察内容/描述/证据列表）
        cols = [r["name"] for r in conn.execute("PRAGMA table_info(memories)").fetchall()]
        if "observation" not in cols:
            conn.execute("ALTER TABLE memories ADD COLUMN observation TEXT")
        if "description" not in cols:
            conn.execute("ALTER TABLE memories ADD COLUMN description TEXT")
        if "evidence" not in cols:
            conn.execute("ALTER TABLE memories ADD COLUMN evidence TEXT")
        if "archived_at" not in cols:
            conn.execute("ALTER TABLE memories ADD COLUMN archived_at TEXT")
        conn.commit()

    def replace_all(self, data):
        """清空并写入整份记忆数据（按 id 保留既有向量）"""
        with self._lock:
            conn = self.connect()
            # 先取出旧向量（id -> BLOB），整表重写时按 id 还原，避免向量丢失
            old_vec = {}
            try:
                for r in conn.execute("SELECT id, embedding FROM memories").fetchall():
                    if r["embedding"]:
                        old_vec[r["id"]] = r["embedding"]
            except Exception:
                old_vec = {}
            conn.execute("DELETE FROM memories")
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

            for item in data.get("topics", []):
                self._insert_item(conn, "topic", item, now, old_vec.get(item.get("id")))
            for item in data.get("events", []):
                self._insert_item(conn, "event", item, now, old_vec.get(item.get("id")))
            for item in data.get("profile", {}).get("traits", []):
                self._insert_trait(conn, item, now, old_vec.get(item.get("id")))
            # 关系形象：以 __relation__ 特殊行持久化（content=标记, observation=总结）
            rel = data.get("profile", {}).get("relation")
            if isinstance(rel, dict) and (rel.get("content") or "").strip():
                conn.execute(
                    "INSERT OR REPLACE INTO memories "
                    "(id, type, content, embedding, importance, access_count,"
                    " last_accessed_at, evidence_count, archived, source, created_at, observation)"
                    " VALUES (?, ?, ?, NULL, ?, 0, ?, ?, 0, '', ?, ?)",
                    ("__relation__", "profile", "__relation__",
                     0.5,  # 关系形象已取消「确信度」，importance 列仅占位
                     rel.get("updated_at", now),
                     int(rel.get("evidence_count", 1)),
                     rel.get("updated_at", now),
                     (rel.get("content") or "").strip()),
                )

            conn.commit()

    def set_embedding(self, item_id, vec):
        """为某条记忆写入/更新向量（vec: np.ndarray）"""
        if item_id is None:
            return
        with self._lock:
            conn = self.connect()
            conn.execute("UPDATE memories SET embedding=? WHERE id=?",
                         (np.asarray(vec, dtype=np.float32).tobytes(), item_id))
            conn.commit()

    def load_embeddings(self):
        """读取全部记忆向量：{id: np.ndarray(float32)}"""
        with self._lock:
            conn = self.connect()
            out = {}
            for r in conn.execute("SELECT id, embedding FROM memories").fetchall():
                b = r["embedding"]
                if b:
                    try:
                        out[r["id"]] = np.frombuffer(b, dtype=np.float32).copy()
                    except Exception:
                        pass
            return out

    def _insert_item(self, conn, type_name, item, now, embedding_blob=None):
        conn.execute(
            """
            INSERT OR REPLACE INTO memories
            (id, type, content, embedding, importance, access_count,
             last_accessed_at, evidence_count, archived, archived_at, source, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                item.get("id") or str(uuid.uuid4())[:8],
                type_name,
                item.get("content", ""),
                embedding_blob,
                float(item.get("importance", 0.5)),
                int(item.get("access_count", 0)),
                item.get("last_accessed_at", now),
                int(item.get("evidence_count", 1)),
                1 if item.get("archived", False) else 0,
                item.get("archived_at"),      # 归档时刻：满 ARCHIVE_TTL_DAYS 天彻底删除
                item.get("source", ""),
                item.get("created_at", now),
            )
        )

    def _insert_trait(self, conn, item, now, embedding_blob=None):
        conn.execute(
            """
            INSERT OR REPLACE INTO memories
            (id, type, content, embedding, importance, access_count,
             last_accessed_at, evidence_count, archived, source, created_at,
             observation, description, evidence)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                item.get("id") or str(uuid.uuid4())[:8],
                "profile",
                item.get("trait", ""),
                embedding_blob,
                float(item.get("confidence", 0.5)),
                int(item.get("evidence_count", 1)),
                item.get("updated_at", now),
                int(item.get("evidence_count", 1)),
                0,
                "",
                item.get("created_at", now),
                item.get("observation", ""),
                item.get("description", ""),
                json.dumps(item.get("evidence") or [], ensure_ascii=False),
            )
        )

    def load_all(self):
        """从数据库读出完整记忆 dict。"""
        with self._lock:
            conn = self.connect()
            rows = conn.execute("SELECT * FROM memories").fetchall()
            topics = []
            events = []
            traits = []
            relation = None

            for row in rows:
                rtype = row["type"]
                if rtype == "topic":
                    topics.append(self._row_to_topic(row))
                elif rtype == "event":
                    events.append(self._row_to_event(row))
                elif rtype == "profile":
                    if row["content"] == "__relation__":
                        relation = {
                            "content": row["observation"] or "",
                            "evidence_count": row["evidence_count"],
                            "updated_at": row["last_accessed_at"],
                        }
                    else:
                        traits.append(self._row_to_trait(row))

            return {
                "topics": topics,
                "events": events,
                "profile": {"traits": traits, "relation": relation},
            }

    def _row_to_topic(self, row):
        return {
            "id": row["id"],
            "content": row["content"],
            "created_at": row["created_at"],
            "last_accessed_at": row["last_accessed_at"],
            "importance": row["importance"],
            "access_count": row["access_count"],
            "evidence_count": row["evidence_count"],
            "archived": bool(row["archived"]),
            "archived_at": row["archived_at"],
        }

    def _row_to_event(self, row):
        return {
            "id": row["id"],
            "content": row["content"],
            "created_at": row["created_at"],
            "last_accessed_at": row["last_accessed_at"],
            "importance": row["importance"],
            "access_count": row["access_count"],
            "evidence_count": row["evidence_count"],
            "archived": bool(row["archived"]),
            "archived_at": row["archived_at"],
            "source": row["source"],
        }

    def _row_to_trait(self, row):
        evidence = []
        try:
            raw = row["evidence"]
            if raw:
                parsed = json.loads(raw)
                if isinstance(parsed, list):
                    evidence = [str(e) for e in parsed if str(e).strip()]
        except Exception:
            evidence = []
        # 兼容旧库：只有 observation 没有 description 的行，观察文本当作描述兜底
        desc = row["description"] or ""
        if not desc:
            desc = row["observation"] or ""
        return {
            "id": row["id"],
            "trait": row["content"],
            "description": desc,
            "evidence": evidence,
            "created_at": row["created_at"],
            "updated_at": row["last_accessed_at"],
        }

    def has_data(self):
        with self._lock:
            conn = self.connect()
            row = conn.execute("SELECT COUNT(*) AS c FROM memories").fetchone()
            return row["c"] > 0
