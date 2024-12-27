# --------------------------------------------------------------------
import contextlib as cl
import itertools as it
import typing as tp
from collections import Counter

from .bxerrors import Reporter
from .bxast    import *
from .bxscope  import Scope

# ====================================================================
SigType    = tuple[tuple[Type], Opt[Type]]
ProcSigMap = dict[str, SigType]

# --------------------------------------------------------------------
class PreTyper:
    def __init__(self, reporter : Reporter):
        self.reporter = reporter

    def pretype(self, prgm : Program) -> tuple[Scope, ProcSigMap]:
        scope = Scope()
        procs = dict()

        for topdecl in prgm:
            match topdecl:
                case ProcDecl(name, arguments, rettype, body, raises):
                    if name.value in procs:
                        self.reporter(
                            f'duplicated procedure name: {name.value}',
                            position = name.position
                        )
                        continue

                    # check if the items in raises are duplicated
                    raise_values = [r.value for r in raises]
                    if len(raise_values) != len(set(raise_values)):
                        self.reporter(
                            f'duplicated exception in raises: {name.value}',
                            position = name.position
                        )
                        continue

                    procs[name.value] = (
                        tuple(tp for _, tp in arguments),
                        rettype if rettype is not None else Type.VOID,
                        raises
                    )

                case GlobVarDecl(name, init, type_):
                    if name.value in scope:
                        self.reporter(
                            f'duplicated global variable name: {name.value}',
                            position = name.position
                        )
                        continue

                    scope.push(name.value, type_)

                case ExceptionDecl(name):
                    if name.value in scope:
                        self.reporter(
                            f'duplicated exception name: {name.value}',
                            position = name.position
                        )
                        continue

                    scope.push(name.value, Type.VOID)

                case _:
                    assert(False)

        # print(procs['main'][0:2])
        if 'main' not in procs:
            self.reporter('this program is missing a main subroutine')
        else:
            if procs['main'][0:2] != ((), Type.VOID):
                self.reporter(
                    '"main" should not take any argument and should not return any value'
                )
            # check if main raises any exception
            if procs['main'][2]:
                self.reporter(
                    '"main" should not raise any exception'
                )

        return scope, procs

# --------------------------------------------------------------------
class TypeChecker:
    B : Type = Type.BOOL
    I : Type = Type.INT

    SIGS = {
        'opposite'                 : ([I   ], I),
        'bitwise-negation'         : ([B   ], B),
        'boolean-not'              : ([B   ], B),
        'addition'                 : ([I, I], I),
        'subtraction'              : ([I, I], I),
        'multiplication'           : ([I, I], I),
        'division'                 : ([I, I], I),
        'modulus'                  : ([I, I], I),
        'logical-right-shift'      : ([I, I], I),
        'logical-left-shift'       : ([I, I], I),
        'bitwise-and'              : ([I, I], I),
        'bitwise-or'               : ([I, I], I),
        'bitwise-xor'              : ([I, I], I),
        'boolean-and'              : ([B, B], B),
        'boolean-or'               : ([B, B], B),
        'cmp-equal'                : ([I, I], B),
        'cmp-not-equal'            : ([I, I], B),
        'cmp-lower-than'           : ([I, I], B),
        'cmp-lower-or-equal-than'  : ([I, I], B),
        'cmp-greater-than'         : ([I, I], B),
        'cmp-greater-or-equal-than': ([I, I], B),
    }

    def __init__(self, scope : Scope, procs : ProcSigMap, reporter : Reporter):
        self.scope                  = scope
        self.procs                  = procs
        self.loops                  = 0
        self.proc                   = None
        self.reporter               = reporter
        self.declared_exceptions    = set()
        self.try_except_block       = []
        self.exception_scopes       = []
        self.raise_stack            = []   # stack to keep track of the function-chain that raises an exception
        self.try_block_except       = []   # stack to keep track of the try-except block

    def report(self, msg: str, position: Opt[Range] = None):
        self.reporter(msg, position = position)

    @cl.contextmanager
    def in_loop(self):
        self.loops += 1
        try:
            yield self
        finally:
            self.loops -= 1

    @cl.contextmanager
    def in_proc(self, proc: ProcDecl):
        assert(self.proc is None)

        self.proc = proc
        self.scope.open()
        try:
            yield self
        finally:
            self.proc = None
            self.scope.close()

    def check_local_free(self, name : Name):
        if self.scope.islocal(name.value):
            self.report(f'duplicated variable declaration for {name.value}')
            return False
        return True

    def check_local_bound(self, name : Name):
        if name.value not in self.scope:
            self.report(
                f'missing variable declaration for {name.value}',
                position = name.position,
            )
            return None
        return self.scope[name.value]

    def check_integer_constant_range(self, value : int):
        if value not in range(-(1 << 63), 1 << 63):
            self.report(f'integer literal out of range: {value}')
            return False
        return True
    
    def for_expression(self, expr : Expression, etype : Opt[Type] = None):
        type_ = None
        match expr:
            case VarExpression(name):
                if self.check_local_bound(name):
                    type_ = self.scope[name.value]

            case BoolExpression(value):
                type_ = Type.BOOL

            case IntExpression(value):
                self.check_integer_constant_range(value)
                type_ = Type.INT

            case OpAppExpression(operator, arguments):
                if operator not in self.SIGS:
                    self.report(f"Unknown operator {operator}")
                else:
                    opsig = self.SIGS[operator]
                    # Check each argument
                    for expected_t, argument_expr in zip(opsig[0], arguments):
                        self.for_expression(argument_expr, etype=expected_t)
                    type_ = opsig[1]

            case CallExpression(proc, arguments):
                if proc.value not in self.procs:
                    self.report(
                        f'unknown procedure: {proc.value}',
                        position = proc.position,
                    )
                else:
                    atypes, retty, raises = self.procs[proc.value]
                    if len(arguments) != len(atypes):
                        self.report(
                            f'invalid number of arguments to {proc.value}: '
                            f'expected {len(atypes)}, got {len(arguments)}',
                            position = expr.position,
                        )
                    # Check each argument type
                    for i, arg_expr in enumerate(arguments):
                        expected_t = atypes[i] if i < len(atypes) else None
                        self.for_expression(arg_expr, etype=expected_t)
                    type_ = retty

                    # if it's a procedure that raises make sure it's inside a try-except block
                    # print(proc)
                    if raises:
                        # print(len(self.try_except_block))
                        if self.proc is None or self.proc.name.value == 'main':
                            if len(self.try_except_block) == 0:
                                self.report(
                                    f"Procedure {proc.value} raises an exception but is not inside a try-except block",
                                    position=expr.position
                                )
                    # if the last function in the raise stack is called add the current function
                    if self.raise_stack:
                        if self.raise_stack[-1][0] == proc.value:
                            self.raise_stack.append((self.proc.name.value, 1 if self.try_except_block else 0))

                    # print(self.raise_stack)

            case PrintExpression(argument):
                self.for_expression(argument)
                if argument.type_ is not None and argument.type_ not in (Type.INT, Type.BOOL):
                    self.report(
                        f'can only print int or bool, not {argument.type_}',
                        position=argument.position
                    )
                type_ = Type.VOID

            case _:
                self.report(f"Unsupported expression node: {expr}")

        # Check if it must match a certain expected type
        if type_ is not None:
            if etype is not None and type_ != etype:
                self.report(
                    f'invalid type: got {type_}, expected {etype}',
                    position=expr.position
                )

        # Store the computed type
        expr.type_ = type_

    def for_statement(self, stmt : Statement):
        match stmt:
            case VarDeclStatement(name, init, type_):
                if self.check_local_free(name):
                    self.scope.push(name.value, type_)
                self.for_expression(init, etype=type_)

            case AssignStatement(lhs, rhs):
                lhstype = self.check_local_bound(lhs)
                self.for_expression(rhs, etype=lhstype)

            case ExprStatement(expression):
                self.for_expression(expression)

            case BlockStatement(body):
                self.for_block(body)

            case IfStatement(condition, then, else_):
                self.for_expression(condition, etype=Type.BOOL)
                self.for_statement(then)
                if else_ is not None:
                    self.for_statement(else_)

            case WhileStatement(condition, body):
                self.for_expression(condition, etype=Type.BOOL)
                with self.in_loop():
                    self.for_statement(body)

            case BreakStatement() | ContinueStatement():
                if self.loops == 0:
                    self.report('break/continue outside of any loop', position=stmt.position)

            case ReturnStatement(expr):
                if expr is None:
                    # must not return a value if the proc has a retty
                    if self.proc and self.proc.rettype is not None:
                        self.report('value-less return in a function')
                else:
                    if self.proc and self.proc.rettype is None:
                        self.report('returning a value in a subroutine')
                    else:
                        self.for_expression(expr, etype=self.proc.rettype)

                # in case I am returning a function that raises an exception
                # ceck if we are in a try-except block
                # yet, we again allow a free float if somewhere down the line there is a try-except block
                # if type(expr) is CallExpression:
                #     # check that the called function raises an exception
                #     _, _, raises = self.procs[expr.proc.value]
                #     if raises:


            case RaiseStatement(exception):
                # print(exception)
                if exception.value not in self.declared_exceptions:
                    self.report(f"Undeclared exception: {exception.value}", position=exception.position)
                
                if len(self.try_except_block) > 0:
                    if exception in self.try_except_block[-1].body:
                        if self.proc is not None:
                            allowed_exceptions = {n.value for n in self.proc.raises}
                            if exception.value not in allowed_exceptions:
                                self.report(
                                    f"{self.proc.name.value} does not declare it raises {exception.value}",
                                    position=exception.position
                                )

                # if a raise statement is encountered in a function check if it is in a try-except block
                # we don't judge any function that floats this freely with the condition that when it is
                # called that is done in a try-except block
                if self.proc is not None:
                    allowed_exceptions = {n.value for n in self.proc.raises}
                    if (exception.value not in allowed_exceptions) and (len(self.try_except_block) == 0):
                        self.report(
                            f"{self.proc.name.value} does not declare it raises {exception.value}",
                            position=exception.position
                        )
                    # also add to the raise stack
                    self.raise_stack.append((self.proc.name.value, 1 if self.try_except_block else 0))

                self.try_block_except.append(exception.value)

            case TryExceptStatement(try_, catches):
                # print(try_)
                self.try_except_block.append(try_)
                self.for_block(try_)
                # self.try_except_block.pop()

                seen_exceptions = set()
                for catch in catches:
                    if catch.exception.value in seen_exceptions:
                        self.report(
                            f"Duplicate catch for exception: {catch.exception.value}",
                            position=catch.position
                        )
                    else:
                        seen_exceptions.add(catch.exception.value)
                    self.for_statement(catch)

                    # when we see a function call inside a try-except block we go throught the call-chain
                    # to see if the function raises an exception
                    if type(catch.body) is CallExpression:
                        _, _, raises = self.procs[catch.body.proc.value]
                        if raises:
                            allowed_exceptions = {n.value for n in raises}
                            if catch.exception.value not in allowed_exceptions:
                                self.report(
                                    f"{catch.body.proc.value} does not declare it raises {catch.exception.value}",
                                    position=catch.position
                                )

                self.try_except_block.pop()
            case CatchStatement(name, body):
                if name.value not in self.declared_exceptions:
                    self.report(
                        f"{name} is not declared as an exception",
                        position=body.position
                    )
                self.for_statement(body)
                if name.value not in self.try_block_except:
                    self.report(
                        f"{name} is unreachable",
                        position=body.position
                    )

            case _:
                print(stmt)
                assert(False)

    def for_block(self, block : Block):
        with self.scope.in_subscope():
            if type(block) is not list:
                block = [block]
            for stmt in block:
                self.for_statement(stmt)

    def for_topdecl(self, decl : TopDecl):
        match decl:
            case ProcDecl(name, arguments, retty, body, raises):
                with self.in_proc(decl):
                    for vnames, vtype_ in arguments:
                        for vname in vnames:
                            if self.check_local_free(vname):
                                self.scope.push(vname.value, vtype_)
                    self.for_statement(body)

                    if retty is not None:
                        if not self.has_return(body):
                            self.report(
                                'this function is missing a return statement',
                                position = decl.position,
                            )
            
            case ExceptionDecl(name):
                # check if the exception is not there yet
                if name.value not in self.declared_exceptions:
                    self.declared_exceptions.add(name.value)
                else:
                    self.report(
                        f'Exception {name.value} already declared',
                        position=name.position
                    )

            case GlobVarDecl(name, init, type_):
                self.for_expression(init, etype = type_)

                if not self.check_constant(init):
                    self.report(
                        'this expression is not a literal',
                        position = init.position,
                    )

    def for_program(self, prgm : Program):
        for decl in prgm:
            self.for_topdecl(decl)

    def check_constant(self, expr: Expression):
        match expr:
            case IntExpression(_):
                return True

            case _:
                return False

    def has_return(self, stmt: Statement):
        # print("Iteration statement ", stmt, '\n')
        match stmt:
            case ReturnStatement(_):
                return True

            case IfStatement(_, iftrue, iffalse):
                return \
                    self.has_return(iftrue) and \
                    self.has_return(iffalse) or \
                    (self.has_return(iftrue) and self.has_raise(iffalse)) or \
                    (self.has_raise(iftrue) and self.has_return(iffalse)) or \
                    (self.has_raise(iftrue) and self.has_raise(iffalse))

            case BlockStatement(block):
                return any(self.has_return(b) for b in block)

            case _:
                return False
            
    def has_raise(self, stmt: Statement):
        match stmt:
            case RaiseStatement(_):
                return True

            case IfStatement(_, iftrue, iffalse):
                return \
                    self.has_raise(iftrue) and \
                    self.has_raise(iffalse)

            case BlockStatement(block):
                return any(self.has_raise(b) for b in block)

            case _:
                return False

    def report(self, msg: str, position: Opt[Range] = None):
        self.reporter(msg, position=position)


    def check(self, prgm: Program):
        # print(prgm)

        for decl in prgm:
            # print("decl ", decl)
            match decl:
                case ExceptionDecl(name):
                    self.declared_exceptions.add(name.value)

                case ProcDecl(name, arguments, rettype, body, raises):
                    with self.in_proc(decl):
                        for vnames, vtype_ in arguments:
                            if type(vnames) is not list:
                                vnames = [vnames]
                            for vname in vnames:
                                if self.check_local_free(vname):
                                    self.scope.push(vname.value, vtype_)
                        # print("body ", body)
                        self.for_statement(body)

                    # check that the raises are declared
                    # print(raises)
                    for r in raises:
                        if r.value not in self.declared_exceptions:
                            self.report(
                                f"Undeclared exception: {r.value}",
                                position=r.position
                            )

                        if rettype is not None:
                            if not self.has_return(body):
                                self.report(
                                    'this function is missing a return statement',
                                    position=decl.position,
                                )

                    # if it has raies add it to exception scopes
                    if raises:
                        # print(decl)
                        self.exception_scopes.append(decl)

                    # print(self.raise_stack)

                case GlobVarDecl(name, init, type_):
                    self.for_expression(init, etype=type_)

                case _:
                    self.report(f"Unknown top-level declaration: {decl}")

        # if every element in the raise stack has the second argument as 0 raise an error
        # print(self.proc)
        flag = 0
        for r in self.raise_stack:
            # print(r)
            if r[1] == 1:
                flag = 1
        if not flag:
            self.report(
                "Some function raises an exception but is not in a try-except block"
            )


        # End of check
        # print(self.declared_exceptions)
        self.reporter.checkpoint()


# --------------------------------------------------------------------
def check(prgm : Program, reporter : Reporter):
    with reporter.checkpoint() as checkpoint:
        scope, procs = PreTyper(reporter).pretype(prgm)
        TypeChecker(scope, procs, reporter).check(prgm)
        return bool(checkpoint)
