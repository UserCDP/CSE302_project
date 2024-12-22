# --------------------------------------------------------------------
import abc
import contextlib as cl
import math
import sys

from typing import Optional as Opt

from .bxast import *

# ====================================================================
class _ReporterContextManager:
    def __init__(self, reporter : 'Reporter'):
        self.cp       = reporter.nerrors
        self.reporter = reporter

    def __bool__(self):
        return self.cp == self.reporter.nerrors

# --------------------------------------------------------------------
class Reporter(abc.ABC):
    def __init__(self, source: str):
        self.source  = source.splitlines()
        self.nerrors = 0

    def __call__(self, message: str, position: Opt[Range] = None):
        self.nerrors += 1
        self._report(message, position)

    @cl.contextmanager
    def checkpoint(self):
        yield _ReporterContextManager(self)

    @abc.abstractmethod
    def _report(self, message: str, position: Opt[Range]):
        pass

# --------------------------------------------------------------------
class DefaultReporter(Reporter):
    def _report(self, message: str, position: Opt[Range]):
        def p(*x):
            print(*x, file = sys.stderr)

        if self.nerrors > 1:
            p()

        if position is None:
            p(message)
        else:
            width = max(2, math.ceil(math.log(len(self.source)+1, 10)))

            if position.start[0] == position.end[0]:
                p(f'line {position.start[0]}: {message}')

                l2 = position.start[0] - 1
                l1 = max(l2-2, 0)
                c  = (position.start[1], position.end[1])

            else:
                p(f'lines {position.start[0]}--{position.end[0]}: {message}')
        
                l1 = position.start[0] - 1
                l2 = position.end[0]-1
                c  = None

            p()

            for i in range(l1, l2+1):
                p(f'| {i+1:0{width}}:', self.source[i])

            if c is not None:
                print(' ' * (c[0]+width+3), '^' * (c[1]-c[0]))
