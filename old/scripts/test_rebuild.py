"""Behavioral checks for the bounded dependency scheduler."""
import threading
import time
import unittest

from rebuild import build_dag


class RebuildTests(unittest.TestCase):
    def test_dependencies_and_concurrency(self):
        dependencies = {"a": set(), "b": set(), "c": {"a"}, "d": {"b", "c"}}
        active = set()
        done = set()
        seen = set()
        peak = 0
        lock = threading.Lock()

        def build(name):
            nonlocal peak
            with lock:
                self.assertLessEqual(dependencies[name], done)
                active.add(name)
                seen.add(name)
                peak = max(peak, len(active))
            time.sleep(0.02)
            with lock:
                active.remove(name)
            return 0

        def completed(name, code):
            self.assertEqual(code, 0)
            with lock:
                done.add(name)

        self.assertTrue(build_dag(list(dependencies), dependencies, 2, build, completed))
        self.assertEqual(seen, set(dependencies))
        self.assertEqual(peak, 2)
        self.assertFalse(active)

    def test_failure_does_not_launch_dependents(self):
        seen = []
        completed = []

        def build(name):
            seen.append(name)
            return 1

        self.assertFalse(build_dag(["a", "b"], {"a": set(), "b": {"a"}}, 2,
                                   build, lambda name, code: completed.append((name, code))))
        self.assertEqual(seen, ["a"])
        self.assertEqual(completed, [("a", 1)])

    def test_cycle_is_rejected(self):
        with self.assertRaises(ValueError):
            build_dag(["a", "b"], {"a": {"b"}, "b": {"a"}}, 2,
                      lambda _: 0, lambda *_: None)


if __name__ == "__main__":
    unittest.main()
