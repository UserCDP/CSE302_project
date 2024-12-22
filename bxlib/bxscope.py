# --------------------------------------------------------------------
import contextlib as cl
import typing as tp

# ====================================================================
class Scope:
    def __init__(self):
        self.vars = [dict()]

    def open(self):
        self.vars.append(dict())

    def close(self):
        assert(len(self.vars) > 0)
        self.vars.pop()

    def push(self, name: str, data: tp.Any):
        assert(name not in self.vars[-1])
        self.vars[-1][name] = data

    def islocal(self, name: str):
        return name in self.vars[-1]
    
    def is_exception(self, name: str):
        return any(name in s for s in self.vars)

    def push_exception(self, name: str, data: tp.Any):
        self.push(name, data)

    def __getitem__(self, name: str):
        for s in self.vars[::-1]:
            if name in s:
                return s[name]
        assert(False)

    def __contains__(self, name: str):
        return any(name in s for s in self.vars)

    @cl.contextmanager
    def in_subscope(self):
        self.open()
        try:
            yield self
        finally:
            self.close()
