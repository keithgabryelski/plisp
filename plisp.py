#!C:/Python25/python.exe
import math, sys, traceback, logging, copy
from enum import Enum
from REI.Text.StringTranslator import StringTranslator
from StringIO import StringIO

__author__  = "Keith Gabryelski <keith@gabryelski.com>"
__status__  = "alpha"
__version__ = "0.9"
__date__    = "27 June 2007"

class Atom(object):
    "An L-Value"

    __slots__ = ("slot", "type", "value", "isConstant")

    Type = Enum("Symbol",
                "Number",
                "String",
                "DottedPair",
                "BuiltinFunction",
                "BuiltinSpecialForm",
                "UserDefinedFunction",
                "UserDefinedSpecialForm")

    class SNode(object):
        __slots__ = ("car", "cdr")

        def __init__(self, car, cdr):
            self.car = car
            self.cdr = cdr

    class SExpressionIterator(object):
        def __init__(self, s_expression):
            self.sExpression = s_expression
            self.n = 0

        def __iter__(self):
            return self

        def next(self):
            if self.sExpression.isNIL():
                raise StopIteration
            if self.sExpression.type != Atom.Type.DottedPair:
                raise NotAListError, \
                      "Element of SExpression indexed at %d is not a DottedPair: %s" % \
                      (self.n, self.sExpression.type)
            element = self.sExpression.element
            self.sExpression = self.sExpression.nextItem
            self.n += 1
            return element

        def __str__(self):
            return "sexitem: %s" % (self.n,)

    def __init__(self, type, value, is_constant = True):
        self.slot = None
        self.type = type
        self.value = value
        self.isConstant = is_constant

    def isNIL(self):
        return self.type == Atom.Type.Symbol and self.value == 0

    def isFunction(self):
        return self.type in [Atom.Type.BuiltinFunction,
                             Atom.Type.UserDefinedFunction]

    def isSpecialForm(self):
        return self.type in [Atom.Type.BuiltinSpecialForm,
                             Atom.Type.UserDefinedSpecialForm]

    def isInvocable(self):
        return self.type in [Atom.Type.BuiltinFunction,
                             Atom.Type.BuiltinSpecialForm,
                             Atom.Type.UserDefinedFunction,
                             Atom.Type.UserDefinedSpecialForm]

    def isBuiltin(self):
        return self.type in [Atom.Type.BuiltinFunction,
                             Atom.Type.BuiltinSpecialForm]

    def isAtom(self):
        return self.type in [Atom.Type.Number, Atom.Type.String, Atom.Type.Symbol]

    def isPureList(self):
        if self.isNIL():
            return True
        try:
            return isinstance(len([item for item in self]), int)
        except NotAListError:
            pass
        return False

    def car():
        def fget(self):
            if self.type not in [Atom.Type.UserDefinedFunction,
                                 Atom.Type.UserDefinedSpecialForm,
                                 Atom.Type.DottedPair]:
                raise TypeError, "Not an SExpression: %s" % (str(self),)
            return self.value.car
        def fset(self, value):
            if self.type not in [Atom.Type.UserDefinedFunction,
                                 Atom.Type.UserDefinedSpecialForm,
                                 Atom.Type.DottedPair]:
                raise TypeError, "Not an SExpression: %s" % (str(self),)

            if value.isPureList() and self in value:
                raise DataIntegrityError, \
                      "Assignment '%s' would create circular reference: %s" % (value, self)
            self.value.car = value
        return locals()
    car = property(**car())

    def cdr():
        def fget(self):
            if self.type not in [Atom.Type.UserDefinedFunction,
                                 Atom.Type.UserDefinedSpecialForm,
                                 Atom.Type.DottedPair]:
                raise TypeError, "Not an SExpression: %s" % (str(self),)
            return self.value.cdr
        def fset(self, value):
            if self.type not in [Atom.Type.UserDefinedFunction,
                                 Atom.Type.UserDefinedSpecialForm,
                                 Atom.Type.DottedPair]:
                raise TypeError, "Not an SExpression: %s" % (str(self),)
            if value.isPureList() and self in value:
                raise DataIntegrityError, \
                      "Assignment '%s' would create circular reference: %s" % (value, self)
            self.value.cdr = value
        return locals()
    cdr = property(**cdr())

    # lambda helpers
    formalParameters = car
    body = cdr

    # parameter helpers
    formalParameter = car
    nextParameter = cdr

    # list helpers
    element = car
    nextItem = cdr

    # evaluation helpers
    function = car
    arguments = cdr

    argument = car
    nextArgument = cdr

    def __iter__(self):
        if not self.isNIL() and self.type != Atom.Type.DottedPair:
            # Cut them off at the pass.
            if isinstance(self, OrdinaryAtom):
                raise NotAListError, \
                      "Not isNIL and type is not DottedPair: name: %s, type: %s" % \
                      (self.name, self.type,)
            else:
                raise NotAListError, \
                      "Not isNIL and type is not DottedPair: type: %s, value: %s" % \
                      (self.type, self.value,)
        return Atom.SExpressionIterator(self)

    def __len__(self):
        return len([item for item in self])

    def __getitem__(self, key):
        if not isinstance(key, int):
            raise KeyError, "Can only handle integers"
        for n,item in enumerate(self):
            if n == key:
                return item
        raise IndexError, "Out of range"

    def __str__(self):
        return "<%s:%s: %s>" % (self.slot, self.type, self.value)

class OrdinaryAtom(Atom):
    "An R-Value"

    __slots__ = ("name", "pList", "bindList")

    def __init__(self, name, type, value, is_constant = False):
        Atom.__init__(self, type, value, is_constant)
        self.name = name
        self.pList = []
        self.bindList = []

    def push(self):
        self.bindList.append((self.type, self.value))

    def pop(self):
        (t, v) = self.bindList.pop()
        self.type = t
        self.value = v

    def __str__(self):
        if self.name != None:
            return "<%s:%s: %s %s>" % (self.slot, self.type, self.name, str(self.value))
        return "<%s:%s: %s>" % (self.slot, self.type, str(self.value))

class AtomTable(object):
    def __init__(self):
        self.__elements = list()
        self.__names = dict()
        self.__numbers = dict()
        self.__strings = dict()

    def __getitem__(self, key):
        if not isinstance(key, int):
            raise KeyError, "Bad type: %s (value: %s)" % (type(key), key,)
        return self.__elements[key]

    def find(self, name):
        return self.__names.get(name, None)

    def findNumber(self, value):
        return self.__numbers.get(value, None)

    def findString(self, text):
        return self.__strings.get(text, None)

    def addToSymbolTable(self, atom):
        self.__elements.append(atom)
        atom.slot = len(self.__elements) - 1

        if isinstance(atom, OrdinaryAtom):
            if atom.name != None:
                self.__names[atom.name] = atom
        elif atom.type == Atom.Type.Number:
            self.__numbers[atom.value] = atom
        elif atom.type == Atom.Type.String:
            self.__strings[atom.value] = atom

        return atom.slot

    #

    def getVariable(self, name):
        atom = self.find(name)
        if atom == None:
            atom = self.createVariable(name)
        return atom

    #

    def createShadowAtom(self, symbol_atom, referenced_atom):
        atom = OrdinaryAtom(symbol_atom.name,
                            referenced_atom.type, referenced_atom.value,
                            referenced_atom.isConstant)
        atom.slot = referenced_atom.slot
        return atom

    def copyAtom(self, atom):
        if atom.isConstant:
            return atom
        return self.createAtom(None, atom.type, atom.value)

    def createAtom(self, name, type, value, is_constant = False):
        atom = OrdinaryAtom(name, type, value, is_constant)
        self.addToSymbolTable(atom)
        return atom

    def createConstantSymbol(self, name, value = None):
        """A named R-value that is immutable. If VALUE is None this constant will
        reference its own slot (index into the AtomTable), if VALUE is
        an Atom then this will reference the value (ensure it is in the AtomTable and
        point to its slot), otherwise VALUE should be an index into the AtomTable."""

        assert name != None, "Symbols must have names"
        
        if isinstance(value, Atom):
            slot = self.getSlot(value)
        elif value == None:
            slot = value
        else:
            assert isinstance(value, int), \
                   "Constant symbol value must be an Atom (or an index into the atom table)"
            slot = value
        atom = OrdinaryAtom(name, Atom.Type.Symbol, slot, True)
        new_slot = self.addToSymbolTable(atom)
        if slot == None:
            atom.value = new_slot
        return atom

    def createVariable(self, name, value = None):
        """A named L-value that is mutable. If VALUE is None then this
        an undefined variable, otherwise VALUE is an index into the AtomTable."""

        assert name != None, "Variables must have names"

        if isinstance(value, Atom):
            slot = self.getSlot(value)
        elif value == None:
            slot = value
        else:
            assert isinstance(value, int), \
                   """A variable's value must an Atom (or an index into the
                   atom table), or None"""
            slot = value
        atom = OrdinaryAtom(name, Atom.Type.Symbol, value, False)
        self.addToSymbolTable(atom)
        return atom

    def createBuiltinFunction(self, name, method):
        """A variable (named L-value) is created and points to atom which is a constant
        function whose value is a method (python code).  This allows builtins
        to be overidden by user defined code -- be careful :-)."""

        atom = self.createAtom("$"+name, Atom.Type.BuiltinFunction, method, True)
        return self.createVariable(name, atom.slot)

    def createBuiltinSpecialForm(self, name, method):
        """A variable (named L-value) is created and points to atom which is a constant
        special function whose value is a method (python code).  This allows builtins
        to be overided by user defined code -- be careful :-)."""

        atom = self.createAtom("$"+name, Atom.Type.BuiltinSpecialForm, method, True)
        return self.createVariable(name, atom.slot)

    def createNumber(self, value):
        assert isinstance(value, (int,float)), \
               "Numbers must have a value of type int or float."
        atom = Atom(Atom.Type.Number, value)
        self.addToSymbolTable(atom)
        return atom

    def createString(self, value):
        assert isinstance(value, str), "Strings must have a value of type str."
        atom = Atom(Atom.Type.String, value)
        self.addToSymbolTable(atom)
        return atom

    def createDottedPair(self, car = None, cdr = None):
        atom = Atom(Atom.Type.DottedPair, Atom.SNode(car, cdr))
        self.addToSymbolTable(atom)
        return atom

    def createUserDefinedFunction(self, name, parameters, body):
        return self.createAtom(name, Atom.Type.UserDefinedFunction,
                               Atom.SNode(parameters, body))

    def createUserDefinedSpecialForm(self, name, parameters, body):
        return self.createAtom(name, Atom.Type.UserDefinedSpecialForm,
                               Atom.SNode(parameters, body))

class Interpreter(object):

    class StackFrame(object):
        interpreter = None

        def __init__(self, function, arguments = None):
            self.functionName = function.name
            self.isBuiltin = function.isBuiltin()
            self.isSpecialForm = function.isSpecialForm()
            if self.isBuiltin:
                self.functionBody = str(function.value)
                self.functionParameters = "(UNKNOWN)"
                self.hasVariableArguments = False
            else:
                self.functionBody = copy.copy(function.body)
                if function.formalParameters.isPureList():
                    self.hasVariableArguments = False
                    self.functionParameters = [copy.copy(parameter) for parameter in function.formalParameters]
                else:
                    self.hasVariableArguments = True
                    self.functionParameters = copy.copy(function.formalParameters)
            if arguments != None:
                self.addArguments(arguments)
            else:
                self.functionArguments = None

        def addArguments(self, arguments):
            self.functionArguments = [copy.copy(argument) for argument in arguments]

        def __str__(self):
            if  self.functionArguments == None:
                arguments = "NOTSET"
            else:
                arguments = "\n\t: %s" % \
                            ("\n\t: ".join([self.interpreter.printOut(a) for a in self.functionArguments]),)

            if self.isBuiltin:
                return "%s%s %s" % (("", "&")[self.isSpecialForm], self.functionName, arguments)

            if self.hasVariableArguments:
                parameters = self.functionParameters.name
                return "%s%s *%s = %s" % (("", "&")[self.isSpecialForm], self.functionName, parameters, arguments)

            parameters = "(%s)" % (" ".join([p.name for p in self.functionParameters]),)

            return "%s%s %s = %s" % (("", "&")[self.isSpecialForm], self.functionName, parameters, arguments)

            #return "%s %s = %s: %s" % (self.functionName, parameters, arguments, self.interpreter.printOut(self.functionBody))

    def __init__(self):
        self.pushedTokens = []
        self.atomTable = AtomTable()
        self.context = []
        self._resetDebugStack()
        Interpreter.StackFrame.interpreter = self

    def _getLastDebugStackFrame(self):
    	return self.debugStack[len(self.debugStack) - 1]

    def _createDebugStackFrame(self, function):
        return Interpreter.StackFrame(function)

    def _pushDebugStack(self, stack_frame):
        self.debugStack.append(stack_frame)
        if len(self.debugStack) > 100:
            raise InfiniteLoopDetectedError, "Bummer"
        
    def _popDebugStack(self):
        self.debugStack.pop()

    def _dumpDebugStack(self):
        for n,stack_frame in enumerate(self.debugStack):
            print "%d: %s" % (n, str(stack_frame))

    def _resetDebugStack(self):
        self.debugStack = []

    def initialize(self):
        # Order of operations is important here.
        # NIL must be slot 0
        # T is less important.

        self.NIL = self.atomTable.createConstantSymbol("nil")
        self.T = self.atomTable.createConstantSymbol("t")

        # minimal set

        self.atomTable.createBuiltinSpecialForm("quote", self.QUOTE)
        self.atomTable.createBuiltinFunction("atom", self.ATOM)
        self.atomTable.createBuiltinFunction("eq", self.EQ)
        self.atomTable.createBuiltinFunction("cons", self.CONS)
        self.atomTable.createBuiltinFunction("car", self.CAR)
        self.atomTable.createBuiltinFunction("cdr", self.CDR)
        self.atomTable.createBuiltinSpecialForm("cond", self.COND)
        self.atomTable.createBuiltinSpecialForm("lambda", self.LAMBDA)
        self.atomTable.createBuiltinSpecialForm("label", self.LABEL)

        # more required

        self.atomTable.createBuiltinFunction("set", self.SET)
        self.atomTable.createBuiltinSpecialForm("setq", self.SETQ)
        self.atomTable.createBuiltinFunction("plus", self.PLUS)
        self.atomTable.createBuiltinFunction("difference", self.DIFFERENCE)
        self.atomTable.createBuiltinFunction("minus", self.MINUS)
        self.atomTable.createBuiltinFunction("times", self.TIMES)
        self.atomTable.createBuiltinFunction("quotient", self.QUOTIENT)
        self.atomTable.createBuiltinFunction("power", self.POWER)
        self.atomTable.createBuiltinFunction("floor", self.FLOOR)
        self.atomTable.createBuiltinFunction("integer", self.INTEGER)
        self.atomTable.createBuiltinFunction("eval", self.EVAL)
        self.atomTable.createBuiltinFunction("numberp", self.NUMBERP)


        self.atomTable.createBuiltinFunction("list", self.LIST)
        self.atomTable.createBuiltinSpecialForm("and", self.AND)
        self.atomTable.createBuiltinSpecialForm("or", self.OR)

        self.atomTable.createBuiltinSpecialForm("special", self.SPECIAL)

        self.atomTable.createBuiltinFunction("greaterp", self.GREATERP)
        self.atomTable.createBuiltinFunction("lessp", self.LESSP)
        self.atomTable.createBuiltinFunction("gte", self.GTE)
        self.atomTable.createBuiltinFunction("lte", self.LTE)

        self.atomTable.createBuiltinFunction("body", self.BODY)

        self.atomTable.createBuiltinFunction("do", self.DO)

        self.atomTable.createBuiltinFunction("putprop", self.PUTPROP)
        self.atomTable.createBuiltinFunction("getprop", self.GETPROP)
        self.atomTable.createBuiltinFunction("remprop", self.REMPROP)

        self.atomTable.createBuiltinSpecialForm("typeof", self.TYPEOF)
        self.atomTable.createBuiltinFunction("_atomtable", self._ATOMTABLE)
        self.atomTable.createBuiltinFunction("print", self.PRINT)

        self.parse("""
        (setq apply (lambda (apply$function-name apply$formal-parameters)
        	(eval (cons apply$function-name apply$formal-parameters))))

        (setq defun (special (defun$function-name defun$formal-parameter-list defun$function-body)
        	(set defun$function-name (apply 'lambda (list defun$formal-parameter-list defun$function-body)))))

        (setq defspec (special (defun$function-name defun$formal-parameter-list defun$function-body)
        	(set defun$function-name (apply 'special (list defun$formal-parameter-list defun$function-body)))))

        (defun caar (l) (car (car l)))
        (defun cadar (l) (car (cdr (car l))))
        (defun caddr (l) (car (cdr (cdr l))))
        (defun cadr (l) (car (cdr l)))
        (defun cdadr (l) (cdr (car (cdr l))))
        (defun cdar (l) (cdr (car l)))
        (defun cddar (l) (cdr (cdr (car l))))
        (defun cddr (l) (cdr (cdr l)))

        (setq + plus)
        (defun 1+ (x) (+ x 1))
        (setq ++ 1+)
        (setq - difference)
        (defun 1- (x) (- x 1))
        (setq -- 1-)
        (setq / quotient)
        (setq * times)
        (setq = setq)
        (setq == eq)
        (defun != (a b) (not eq(a b)))
        (setq lt lessp)
        (setq < lessp)
        (setq <= lte)
        (setq gt greaterp)
        (setq > greaterp)
        (setq >= gte)

        (defun not (x) (eq x nil))
        (setq ! not)
        (setq null not)

        (defun length (x)
            (cond
              ((null x) 0)
              (t (plus 1 (length (cdr x))))))

        (setq len length)

        (defspec if (a b c)
	            (cond
            		((eval a) (eval b))
                        (t (eval c))))

        (defun lastp (l) (<= (length l) 1))

        (defspec progn
                   list-of-lambdas
                       (cond
                           ((lastp list-of-lambdas) (eval (car list-of-lambdas)))
                           ((and (eval (car list-of-lambdas)) nil) nil)
                           (t (apply 'progn (cdr list-of-lambdas)))))

        (defun sum l
       	     (if (null l)
                  0
                  (plus (car l) (apply 'sum (cdr l)))))

        (defun append (x y) (cond ((eq x nil) y)
        			((atom x) (cons x y))
                                (t (cons (car x) (append (cdr x) y)))))

        (defun reverse (x) (cond
		              ((atom x) x)
		              (t (append (reverse (cdr x)) (cons (car x) nil)))))

        (defun equal (x y) (cond
		            ((or (atom x) (atom y)) (eq x y))
		            ((equal (car x) (car y)) (equal (cdr x) (cdr y)))
		            (t nil)))

        (defun fact (x) (cond
        			((eq x 0) 1)
                                (t (times x (fact (difference x 1))))))

        (defun listp (s) (cond ((atom s) (eq s nil)) (t (listp (cdr s)))))

        (defun member (a s)
          (cond ((eq s nil) nil)
            ((equal a (car s)) t)
              (t (member a (cdr s)))))

        (defun place (a s)
          (cond ((eq s nil) nil)
            ((equal a (car s)) (cdr s))
              (t (member a (cdr s)))))

        (defun deepmem (a s)
          (cond ((atom s) nil)
            ((or (equal a (car s)) (deepmem a (car s))) t)
            (t (deepmem a (cdr s)))))

        (defun trunc (s)
            (cond ((eq (length (cdr s)) 1) nil)
              (t (append (car s) (trunc (cdr s))))))

        (defun max s
            (cond ((null s) 0)
            	  ((atom s) s)
                  (t (progn
              	  	(setq max-cdr (apply 'max (cdr s)))
                        (if (gt (car s) max-cdr)
                             (car s)
                             max-cdr)))))
        (defun min s
            (cond ((null s) 0)
            	  ((atom s) s)
                  (t (progn
              	  	(setq min-cdr (apply 'min (cdr s)))
                        (if (lt (car s) min-cdr)
                             (car s)
                             min-cdr)))))

        (defun depth (s)
	          (if (null s) 0
                      (if (atom (car s)) (max 1 (max-depth (cdr s)))
                      (max (1+ (max-depth (car s))) (max-depth (cdr s))))))

        (defun flatp (s)
	           (if (null s)
                        t
                        (if (not (atom (car s)))
                          nil
                          (flatp (cdr s)))))

        (defun flat (s)
        	(if (atom s)
                     s
                     (append (flat (car s)) (flat (cdr s)))))

        (defun into (g l)
          (cond ((null l) l)
          	 (t (cons (g (car l)) (into g (cdr l))))))

        (defun onto (g l)
            (cond ((null l) l)
                  (t (cons (g l) (onto g (cdr l))))))

        (defun product l
       	     (if (null l)
                  0
                  (times (car l) (apply 'product (cdr l)))))

        (defspec evalquote (x) (eval x))

        (defun pure (x)
        	(cond
                	((null x) t)
                        ((atom x) t)
                        ((null (cdr x)) (pure (car x)))
                        ((and
                            (not (atom (cdr x)))
                            (pure (car x))
                            (pure (cdr x)))
                           t)
                         (t  nil)))

       (defun modulo (a n) (- a (* n (floor (/ a n)))))
       (defun zerop (n) (eq n 0))

       ;(defspec if (a b c)
       ;            (cond
       ;    		((eval a) (eval b))
       ;                (t (eval c))))

       (defun gcd (a b)
	     (if (zerop b)
                  a
		  (gcd b (modulo a b))))
        """)

        self.nop("""

        ;;; function GCD

        ;;; stolen from Joe Ganley

        (define flatten (s)
           (cond ((null s) nil)
              ((atom (car s)) (cons (car s) (flatten (cdr s))))
                 (t (append (flatten (car s)) (flatten (cdr s))))))

        ;;; Portions copyright (c) 1988, 1990 Roger Rohrbach

        (define last (e) (cond ((atom e) nil) ((null (cdr e)) (car e)) (t (last (cdr e)))))
        (define remove (e l)
                       (cond ((null l) nil)
                             ((equal e (car l)) (remove e (cdr l)))
                             (t (cons (car l) (remove e (cdr l))))))
        (define mapcar (f l)
             (cond ((null l) nil) (t (cons (eval (list f (list (quote quote (car l))))) (mapcar f (cdr l))))))

        """)

    def interpret(self):
        _logger = logging.getLogger("lisp.interpreter.mainloop")
        print "PLisp v%s:%s [%s] by %s" % (__version__, __status__, __date__, __author__)
        self.parser = LexicalParser(None)
        self.pushedTokens = []
        while True:
            _logger.info("parsing...")
            try:
                s_expression = self.parseSExpression()
            except ParserError, e:
                print e
                continue
            if s_expression == None:
                break
            _logger.info("parsed: %s" % (self.printOut(s_expression),))
            try:
                value = self.v(s_expression)
                _logger.info("evaluted: %s" % (self.printOut(value),))
            except InfiniteLoopDetectedError, ilde:
                print "ERROR: %s" % (ilde,)
                self._dumpDebugStack()
                self._resetDebugStack()
                return
            except UndefinedVariableError, uve:
                print uve
                self._dumpDebugStack()
                self._resetDebugStack()
                continue
            except InvalidExpressionError, iee:
                print "%s: %s" % (iee, self.printOut(s_expression))
                self._dumpDebugStack()
                self._resetDebugStack()
                continue
            except LispError, le:
                traceback.print_exc()
                self._dumpDebugStack()
                self._resetDebugStack()
                continue
            except Exception, e:
                traceback.print_exc()
                self._dumpDebugStack()
                self._resetDebugStack()
                continue

            print self.printOut(value)

    def parse(self, text):
        self.prepareParser(text)
        while True:
            try:
                s_expression = self.parseSExpression()
            except ParserError, e:
                traceback.print_exc()
                print e
                return False
            if s_expression == None:
                return True
            try:
                self.v(s_expression)
            except InfiniteLoopDetectedError, ilde:
                print "ERROR: %s" % (ilde,)
                return False
            except LispError, e:
                traceback.print_exc()
                print "Expression: %s" % (self.printOut(s_expression),)
                return False
            except Exception, e:
                traceback.print_exc()
                print "Expression: %s" % (self.printOut(s_expression),)
                return False

    def nop(self, *args):
        pass

    def parse1(self, text):
        self.prepareParser(text)
        return self.parseSExpression()

    def parseTokens(self, text):
        self.prepareParser(text)
        tokens = []
        while True:
            token = self.getParserToken()
            if token == None:
                return tokens
            tokens.append(token)

    def prepareParser(self, text):
        self.parser = LexicalParser(text)

    def pushTokens(self, *arguments):
        tokens = []
        tokens.extend(arguments)
        tokens.extend(self.pushedTokens)
        self.pushedTokens = tokens

    def getParserToken(self):
        _logger = logging.getLogger("lisp.parser.lexical")
        if len(self.pushedTokens) > 0:
            token = self.pushedTokens.pop(0)
            _logger.info("Popped: %s" % (token,))
            return token
        token = self.parser.getToken()
        if token == None:
            _logger.info("EOF")
            # end of input
            return None
        elif token == "(":
            _logger.info("(")
            return TokenType.OpenParenthesis
        elif token == ")":
            _logger.info(")")
            return TokenType.CloseParenthesis
        elif token == ".":
            _logger.info(".")
            return TokenType.Dot
        elif token == "'":
            _logger.info("'")
            return TokenType.Quote
        elif token[0] == '"':
            _logger.info("String: %s" % (token,))
            return self.atomTable.createString(token)
        elif token[0] in "0123456789." or (token[0] == "-" and token[1:2] in "0123456789."):
            try:
                # Numbers are:
                #      -?([0-9]+.?[0-9]*)|([0-9]*.[0-9]+)|([0-9]*.?[0-9]+)
                # Which is:
                # 	digits
                # 	.digits
                # 	digits.digits
                # 	-digits
                # 	-.digits
                # 	-digits.digits
                # A symbol is anything else (so we can support 1+, 1-, -)
                if "." in token:
                    number = float(token)
                else:
                    number = int(token)
                _logger.info("Number: %s" % (token,))
                return self.atomTable.createNumber(number)
            except:
                # non-numbers are names :-)
                pass
        _logger.info("Symbol: %s" % (token,))
        return self.atomTable.getVariable(token)
        
    def parseSExpression(self):
        token = self.getParserToken()
        if token == None:
            return None
        s_expression = self._parseSExpression(token)
        if s_expression == None:
            raise ParserError, "Too many End Parenthesis"
        return s_expression

    def _parseSExpression(self, token):
        _logger = logging.getLogger("lisp.parser")
        if token == None:
            raise ParserError, "End of input reached before end of expression."

        if isinstance(token, Atom):
            # single atom case
            _logger.info("Atom: %s" % (token,))
            return token
        elif token == TokenType.OpenParenthesis:
            _logger.info("Parsing SExpression")
            # cases:
            #  ( )
            #  ( x )
            #  ( x . y )
            #  ( x y z ETC )

            car = self._parseSExpression(self.getParserToken())
            if car == None:
                # ( ) case - return ATOM: NIL
                _logger.info("Empty List: ( )")
                return self.NIL

            _logger.debug("( %s *" % (car,))
            rootSnode = snode = self.atomTable.createDottedPair(car, self.NIL)

            # check ( x . y )
            token = self.getParserToken()
            if token == TokenType.Dot:
                _logger.debug("( %s . " % (snode.car,))
                snode.cdr = self.parseSExpression()
                if snode.cdr == None:
                    raise ParserError, "Bad dot notation '( x . )'"
                token = self.getParserToken()
                _logger.debug("( %s . %s *" % (snode.car, snode.cdr,))
                if token != TokenType.CloseParenthesis:
                    raise ParserError, "Extra characers in dot notation ( x . y EXTRA )"
                _logger.info("( %s . %s )" % (snode.car, snode.cdr,))
                return snode

            # starting one of:
            # ( x )
            # ( x y ETC )
            while True:
                cdr = self._parseSExpression(token)
                if cdr == None:
                    # got end parenthesis
                    snode.cdr = self.NIL
                    _logger.debug("* )")
                    _logger.info("%s" % (rootSnode,))
                    return rootSnode
                _logger.debug("* %s" % (cdr,))
                snode.cdr = self.atomTable.createDottedPair(cdr, self.NIL)
                snode = snode.cdr
                token = self.getParserToken()
        elif token == TokenType.CloseParenthesis:
            # end of expression
            _logger.info("End of SExpression")
            return None
        elif token == TokenType.Quote:
            # special quote syntax
            # start from base parseSExpresion to catch ')
            s_expression = self.parseSExpression()
            if s_expression == None:
                raise InvalidExpressionError, "Quote without subordinate S-expression"
            self.pushTokens(TokenType.OpenParenthesis,
                            self.atomTable.getVariable("quote"), s_expression,
                            TokenType.CloseParenthesis)
            _logger.info("Pushing (quote s_expression)")
            return self.parseSExpression()
        elif token == TokenType.Dot:
            # . y )
            raise ParserError, "Bad dot notation ' . y )'"
        raise ParserError, "Unknown token type: '%s'" % (token,)

    def printOut(self, s_expression):
        _logger = logging.getLogger("lisp.interpreter.printout")
        _logger.info("printOut: called %s" % (s_expression,))

        if s_expression.type == Atom.Type.Symbol:
            _logger.debug("returning symbol")
            return s_expression.name
        elif s_expression.type == Atom.Type.Number:
            _logger.debug("returning number")
            return str(s_expression.value)
        elif s_expression.type == Atom.Type.String:
            _logger.debug("returning string")
            return repr(s_expression.value)
        elif s_expression.type == Atom.Type.DottedPair:
            if s_expression.isPureList():
                _logger.debug("returning list")
                return "(%s)" % (" ".join([self.printOut(s) for s in s_expression]))
            _logger.debug("returning dot notation")
            return "(%s . %s)" % (self.printOut(s_expression.car),
                                  self.printOut(s_expression.cdr),)

        if isinstance(s_expression, OrdinaryAtom):
            _logger.debug("returning named %s" % (s_expression.type,))
            return "{%s: %s}" % (s_expression.type, s_expression.name)
        return "{%s}" % (s_expression.type)

    #

    def printOut2(self, s_expression):
        _logger = logging.getLogger("lisp.interpreter.printout")
        _logger.info("printOut2: called %s" % (s_expression,))

        if s_expression.type == Atom.Type.Symbol:
            _logger.debug("returning symbol")
            return s_expression.name
        elif s_expression.type == Atom.Type.Number:
            _logger.debug("returning number")
            return str(s_expression.value)
        elif s_expression.type == Atom.Type.String:
            _logger.debug("returning string")
            return repr(s_expression.value)
        elif s_expression.type == Atom.Type.DottedPair:
            if s_expression.isPureList():
                _logger.debug("returning list")
                return "(%s)" % (" ".join([self.printOut3(s) for s in s_expression]))
            _logger.debug("returning dot notation")
            return "(%s . %s)" % (self.printOut2(s_expression.car),
                                  self.printOut2(s_expression.cdr),)
        elif s_expression.isBuiltin():
            return "{%s: %s}" % (s_expression.type, s_expression.name)
        elif s_expression.isFunction():
            return "(LAMBDA %s %s)" % (self.printOut(s_expression.formalParameters),
                                       self.printOut2(s_expression.body))
        elif s_expression.isSpecialForm():
            return "(SPECIAL %s %s)" % (self.printOut(s_expression.formalParameters),
                                        self.printOut2(s_expression.body))
        if isinstance(s_expression, OrdinaryAtom):
            _logger.debug("returning named %s" % (s_expression.type,))
            return "{%s: %s}" % (s_expression.type, s_expression.name)
        return "{%s}" % (s_expression.type)

    #

    def printOut3(self, s_expression):
        _logger = logging.getLogger("lisp.interpreter.printout")
        _logger.info("printOut3: called %s" % (s_expression,))

        if s_expression.type == Atom.Type.Symbol:
            _logger.debug("returning symbol")
            return s_expression.name
        elif s_expression.type == Atom.Type.Number:
            _logger.debug("returning number")
            return str(s_expression.value)
        elif s_expression.type == Atom.Type.String:
            _logger.debug("returning string")
            return repr(s_expression.value)
        elif s_expression.type == Atom.Type.DottedPair:
            if s_expression.isPureList():
                _logger.debug("returning list")
                return "(%s)" % (" ".join([self.printOut3(s) for s in s_expression]))
            _logger.debug("returning dot notation")
            return "(%s . %s)" % (self.printOut3(s_expression.car),
                                  self.printOut3(s_expression.cdr),)

        if isinstance(s_expression, OrdinaryAtom):
            _logger.debug("returning named %s" % (s_expression.type,))
            return "%s" % (s_expression.name,)
        return "{%s}" % (s_expression.type)

    #

    _indent = 0

    def v(self, x):
        _logger = logging.getLogger("lisp.interpreter.v")
        _traceLogger = logging.getLogger("lisp.interpreter.v.trace")
        _logger.info("Evaluating: %s" % (self.printOut(x),))

        if x.type == Atom.Type.DottedPair:
            # Got a dotted pair, which is a function invocation:
            #   (function . arguments)
            # which is:
            #   (function arg1 arg2 arg3 ...)
            # as:
            #   (plus 1 2)
            # CAR must be a function or special form
            function = self.v(x.function)
            if not function.isInvocable():
                raise InvalidExpressionError, \
                      "Expected function or special form: %s = v[%s]" % \
                      (self.printOut(function), self.printOut(x))

            # CDR are the arguments
            arguments = [s for s in x.arguments]

            if _logger.isEnabledFor(logging.DEBUG):
                _logger.debug("Evaluating Function: %s" % (function.name,))
                for n,argument in enumerate(arguments):
                    _logger.debug("Argument:%d: %s" % (n, self.printOut(argument)))

            if not function.isBuiltin():
                # Save symbols used as parameters for user-defined
                # functions
                self.pushParameters(function)

            stack_frame = self._createDebugStackFrame(function)
            self._pushDebugStack(stack_frame)

            if function.isFunction():
                # evaluate arguments for functions (special forms, by
                # definition) do not have their arguments evaluated
                # before invocation.

                arguments = [self.v(argument) for argument in arguments]
                stack_frame.addArguments(arguments)
                if _logger.isEnabledFor(logging.DEBUG):
                    _logger.debug("Evaluated Arguments: %s" % (function.name,))
                    for n,argument in enumerate(arguments):
                        _logger.debug("Argument:%d: %s" % (n, self.printOut(argument)))
            else:
                stack_frame.addArguments(arguments)

            if function.isBuiltin():
                # Builtin functions/special forms are
                # invoked via a python method call.
                _logger.debug("Invoking Builtin %s(%s)" % (function.name, arguments,))

                _traceLogger.info("%s(%s %s)" % ("  " * self._indent,
                                                 function.name,
                                                 " ".join([self.printOut2(a) for a in arguments]),))
                self._indent += 1

                value = function.value(*arguments)

                self._indent -= 1

                _traceLogger.info("%s= %s" % ("  " * self._indent, self.printOut2(value)))

                self._popDebugStack()
                _logger.info("%s: returning: %s" % (function.type, self.printOut(value),))

                return value

            # this is a user defined function or special form
            # assign argument values to parameters

            self.applyArguments(function, arguments)

            # invoke
            _logger.debug("Invoking User Defined %s(%s)" % (function.name, arguments,))

            _traceLogger.info("%s(%s %s)" % ("  " * self._indent,
                                             function.name,
                                             " ".join(["%s!%s" % (self.printOut2(p), self.printOut2(self.atomTable[p.value]),) for p in function.formalParameters]),))

            self._indent += 1

            value = self.v(function.body)

            self._indent -= 1

            _traceLogger.info("%s= %s" % ("  " * self._indent, self.printOut2(value)))

            self._popDebugStack()

            # restore original parameter values
            # so we don't affect our container
            # environment
            self.popParameters(function)

            _logger.info("%s: returning: %s" % (function.type, self.printOut(value),))
            return value
        elif x.type in [Atom.Type.Number, Atom.Type.String]:
            _logger.info("returning: %s, %s" % (x.type, x.value,))
            return x
        elif x.type == Atom.Type.Symbol:
            # a symbol points to something in the AtomTable
            if x.value == None:
                raise UndefinedVariableError, "%s is undefined" % (x.name,)
            p = self.atomTable[x.value]
            if p.isInvocable():
                # create a temporary so we can know
                # the name this was invoked as
                return self.atomTable.createShadowAtom(x, p)
            return p
        elif x.type in [Atom.Type.BuiltinFunction,
                        Atom.Type.BuiltinSpecialForm]:
            _logger.info("%s: returning: %s" % (x.type, x.value.func_name,))
            return x
        elif x.type in [Atom.Type.UserDefinedFunction,
                        Atom.Type.UserDefinedSpecialForm]:
            _logger.info("%s: returning: %s" % (x.type, self.printOut(x),))
            return x
        raise TypeError, \
              "Undefined type passed to v: '%s', type: %s, value: %s" % \
              (x.name, x.type, x.value,)

    #

    def CheckArguments(self, name = None, extras = [], *arguments):
        _logger = logging.getLogger("lisp.interpreter.builtin")
        if _logger.isEnabledFor(logging.DEBUG):
            _logger.debug("Checking Arguments: %s" % (name,))
            for n,argument in enumerate(arguments):
                _logger.debug("Argument:%d: %s" % (n, self.printOut(argument)))
            for n,extra in enumerate(extras):
                _logger.debug("Extra:%d: %s" % (n, self.printOut(extra)))

        for n,argument in enumerate(arguments):
            #argument.checkSExpressionForCircleReference()
            if argument == None:
                raise WrongNumberOfArgumentsError, \
                      "%s: Not enough arguments, expected %d, got %d [%s]" % \
                      (name, len(arguments), n, arguments)

        if len(extras) > 0:
            raise WrongNumberOfArgumentsError, \
                  "%s: Too many arguments, expected %d, got %d [%s]" % \
                  (name, len(arguments), len(arguments) + len(extras), arguments)

    #

    def SET(self, x = None, y = None, *extras):
        self.CheckArguments("set", extras, x, y)
        if x.isConstant:
            raise TypeError, "Can't assign to constant: %s" % (x,)
        x.type = y.type
        x.value = y.value
        return x

    #
    
    def SETQQ(self, x = None, y = None, *extras):
        self.CheckArguments("setqq", extras, x, y)
        if x.isConstant:
            raise TypeError, "Can't assign to constant: %s" % (x,)
        x.type = Atom.Type.Symbol
        x.value = y.slot
        #print "SETQQ '%s %s:%s" % (x.name, x.type, x.value)
        return x

    def SETQ(self, x = None, y = None, *extras):
        self.CheckArguments("setq", extras, x, y)
        if x.isConstant:
            raise TypeError, "Can't assign to constant: %s" % (x,)

        y = self.v(y)

        if x.type == Atom.Type.Symbol:
            if y.type == Atom.Type.Symbol:
                x.value = y.value
            else:
                x.value = y.slot
        else:
            raise TypeError, "Unexpected setq car: %s" % (self.printOut(x),)
        #x.type = y.type
        #x.value = y.value
        return x

    def QUOTE(self, x = None, *extras):
        self.CheckArguments("quote", extras, x)
        return x

    def PLUS(self, n = None, m = None, *extras):
        self.CheckArguments("plus", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.atomTable.createNumber(n.value + m.value)

    def DIFFERENCE(self, n = None, m = None, *extras):
        self.CheckArguments("difference", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.atomTable.createNumber(n.value - m.value)

    def MINUS(self, n = None, *extras):
        self.CheckArguments("minus", extras, n)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        return self.atomTable.createNumber(-n.value)

    def TIMES(self, n = None, m = None, *extras):
        self.CheckArguments("times", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.atomTable.createNumber(n.value * m.value)

    def QUOTIENT(self, n = None, m = None, *extras):
        self.CheckArguments("quotient", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.atomTable.createNumber(n.value / m.value)

    def POWER(self, n = None, m = None, *extras):
        self.CheckArguments("power", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.atomTable.createNumber(pow(n.value, m.value))

    def FLOOR(self, n = None, *extras):
        self.CheckArguments("floor", extras, n)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        return self.atomTable.createNumber(math.floor(n.value))

    def INTEGER(self, n = None, *extras):
        self.CheckArguments("integer", extras, n)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        return self.atomTable.createNumber(int(n.value))

    def EVAL(self, x = None, *extras):
        self.CheckArguments("eval", extras, x)
        value = self.v(x)
        return value

    def EQ(self, x = None, y = None, *extras):
        self.CheckArguments("eq", extras, x, y)
        return self.predicate(x.type == y.type and x.value == y.value)

    def NUMBERP(self, x = None, *extras):
        self.CheckArguments("numberp", extras, x)
        return self.predicate(x.type == Atom.Type.Number)

    def ATOM(self, x = None, *extras):
        self.CheckArguments("atom", extras, x)
        return self.predicate(x.isAtom())

    def CONS(self, x = None, y = None, *extras):
        self.CheckArguments("cons", extras, x, y)
        return self.atomTable.createDottedPair(x, y)

    def CAR(self, x = None, *extras):
        self.CheckArguments("car", extras, x)
        if x.type == Atom.Type.DottedPair:
            return x.car
        return self.NIL

    def CDR(self, x = None, *extras):
        self.CheckArguments("cdr", extras, x)
        if x.type == Atom.Type.DottedPair:
            return x.cdr
        return self.NIL

    #

    def LIST(self, *arguments):
        if len(arguments) == 0:
            return self.NIL
        return self.CONS(arguments[0], self.LIST(*arguments[1:]))

    def AND(self, *arguments):
        for argument in arguments:
            value = self.v(argument)
            if value.isNIL():
                return self.NIL
        return self.T

    def OR(self, *arguments):
        for argument in arguments:
            value = self.v(argument)
            if not value.isNIL():
                return value
        return self.NIL

    def COND(self, *arguments):
        for n,argument in enumerate(arguments):
            if len(argument) != 2:
                raise InvalidExpressionError, \
                      """COND: each argument must be a two element list
                      (COND (test1 value1) (test2 value2) (t certain-value))"""

            conditional = self.v(argument[0])

            if not conditional.isNIL():
                return_value = self.v(argument[1])
                return return_value

        return self.NIL

    #

    def LABEL(self, g, h, *extras):
        self.CheckArguments("label", extras, g, h)
        if not g.isAtom() or g.isConstant:
            raise InvalidExpressionError, \
                  "(LABEL %s %s): first parameter must be a non-constant atom." % (g, h)
        g.push()
        g.type = Atom.Type.Symbol
        assert h.slot != None, \
               "Can not assign label to unregistered S-Expression: %s, %s" % \
               (h, self.printOut(h))
        g.value = h.slot
        value = self.v(h)
        g.pop()
        return value

    def LAMBDA(self, a, b, *extras):
        self.CheckArguments("lambda", extras, a, b)
        if not a.isPureList() and not (a.type == Atom.Type.Symbol and not a.isConstant):
            raise InvalidExpressionError, \
                  "(LAMBDA %s %s): Parameters must be a list or a non-constant variable OrdinaryAtom." % (a, b)
        return self.atomTable.createUserDefinedFunction(None, a, b)

    def SPECIAL(self, a, b, *extras):
        self.CheckArguments("special", extras, a, b)
        if not a.isPureList() and not (a.type == Atom.Type.Symbol and not a.isConstant):
            raise InvalidExpressionError, \
                  "(SPECIAL %s %s): Parameters must be a list or a non-constant variable OrdinaryAtom." % (a, b)
        return self.atomTable.createUserDefinedSpecialForm(None, a, b)

    #

    def GREATERP(self, n = None, m = None, *extras):
        self.CheckArguments("gt", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.predicate(n.value > m.value)

    def LESSP(self, n = None, m = None, *extras):
        self.CheckArguments("lt", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.predicate(n.value < m.value)

    def GTE(self, n = None, m = None, *extras):
        self.CheckArguments("gte", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.predicate(n.value >= m.value)

    def LTE(self, n = None, m = None, *extras):
        self.CheckArguments("lte", extras, n, m)
        if n.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (n,)
        if m.type != Atom.Type.Number:
            raise TypeError, "%s is not number" % (m,)
        return self.predicate(n.value <= m.value)

    #

    def BODY(self, x = None, *extras):
        self.CheckArguments("body", extras, x)
        return self.createAtom(None, Atom.Type.DottedPair, x.value)

    #

    def DO(self, x = None, *extras):
        self.CheckArguments("do", extras, x)
        return x

    def PUTPROP(self, a = None, p = None, v = None, *extras):
        self.CheckArguments("putprop", extras, a, p, v)
        return v

    def GETPROP(self, a = None, p = None, *extras):
        self.CheckArguments("getprop", extras, a, p)
        return self.T

    def REMPROP(self, a = None, p = None, *extras):
        self.CheckArguments("remprop", extras, a, p)
        return self.T
    #

    def _ATOMTABLE(self, *extras):
        for n,atom in enumerate(self.atomTable):
            if isinstance(atom, OrdinaryAtom):
                if atom.name == None:
                    print "%d%s %s %s" % \
                          (n, (":", "!")[atom.isConstant], atom.type, atom.value)
                else:
                    print "%d%s[%s] %s %s" % \
                          (n, (":", "!")[atom.isConstant], atom.name, atom.type,
                           atom.value)
            else:
                print "%d%s %s %s" % \
                      (n, (":", "!")[atom.isConstant], atom.type, atom.value)
        return self.NIL

    def TYPEOF(self, x, *extras):
        self.CheckArguments("typeof", extras, x)
        return self.atomTable.createString("%s:%s" % (type(x), x.type))

    #

    def PRINT(self, *arguments):
        for argument in arguments:
            print self.printOut2(argument),
        print
        return self.NIL

    def predicate(self, expression):
        return (self.NIL, self.T)[bool(expression)]

    #
    def pushContext(self, context):
        print ">%s" % (["%s!%s" % (c.name, self.printOut2(self.atomTable[c.value or 0]),) for c in context])
        self.context.append(context)

    def popContext(self):
        context = self.context.pop()
        print "<%s" % (["%s!%s" % (c.name, self.printOut2(self.atomTable[c.value or 0]),) for c in context])
        return context

    def pushParameters(self, function):
        context = []
        parameters = function.formalParameters
        if parameters.type == Atom.Type.Symbol and parameters.slot != 0:
            # variable number of args
            atom = OrdinaryAtom(parameters.name, parameters.type, parameters.value)
            atom.slot = parameters.slot
            context.append(atom)
        else:
            for n, parameter in enumerate(parameters):
                atom = OrdinaryAtom(parameter.name, parameter.type, parameter.value)
                atom.slot = parameter.slot
                context.append(atom)
        self.pushContext(context)

    def _pushParameters(self, function):
        _logger = logging.getLogger("lisp.interpreter.v.bindlist")
        _logger.debug("<Parameters: %s" % (function.name,))
        parameters = function.formalParameters
        if parameters.type == Atom.Type.Symbol and parameters.slot != 0:
            # variable number of args
            parameters.push()
            _logger.debug("<*: %s" % (parameters.name,))
        else:
            for n, parameter in enumerate(parameters):
                parameter.push()
                _logger.debug("<%d: %s" % (n, parameter.name))

    def applyArguments(self, function, arguments):
        _logger = logging.getLogger("lisp.interpreter.v.bindlist")

        parameters = function.formalParameters
        _logger.debug("=Parameters: %s [%s]" % (function.name, self.printOut(parameters)))
        if parameters.type == Atom.Type.Symbol and parameters.slot != 0:
            # variable number of args
            _logger.debug("=[*%d]: %s %s" % (len(arguments), parameters.name, arguments))
            s_expression = self.LIST(*arguments)
            parameters.value = s_expression.slot
        else:
            if len(parameters) != len(arguments):
                raise WrongNumberOfArgumentsError, \
                      "Expected %d, got %d" % (len(parameters), len(arguments))

            slots = []
            for argument in arguments:
                if argument.type == Atom.Type.Symbol and argument.value != None:
                    slots.append(argument.value)
                else:
                    slots.append(argument.slot)

            #slots = [argument.slot for argument in arguments]

            for n, parameter in enumerate(parameters):
                argument = arguments[n]
                _logger.debug("=%d: %s %s" % (n, parameter.name, self.printOut(argument)))
                parameter.type = Atom.Type.Symbol
                assert argument.slot != None, \
                       "Can not assign parameter to unregistered S-Expression: %s, %s" % \
                       (argument, self.printOut(argument))
                #parameter.value = argument.slot
                parameter.value = slots[n]

            for n, parameter in enumerate(parameters):
                v = self.atomTable[parameter.value]
                _logger.debug("==%d: %s %s" % (n, parameter.name, self.printOut2(v)))


    def popParameters(self, function):
        context = self.popContext()
        for c in context:
            atom = self.atomTable[c.slot]
            atom.type = c.type
            atom.value = c.value

    def _popParameters(self, function):
        _logger = logging.getLogger("lisp.interpreter.v.bindlist")

        _logger.debug(">Parameters: %s" % (function.name,))
        parameters = function.formalParameters
        if parameters.type == Atom.Type.Symbol and parameters.slot != 0:
            # variable number of args
            parameters.pop()
            _logger.debug(">*: %s" % (parameters.name,))
        else:
            for n, parameter in enumerate(parameters):
                parameter.pop()
                _logger.debug(">%d: %s" % (n, parameter.name))


ParserState = Enum("EOF", "Looking", "InSymbol", "InQuotedString", "InEscape")
TokenType = Enum("OpenParenthesis", "CloseParenthesis", "Dot", "Quote")

class LispError(Exception):
    pass

class InfiniteLoopDetectedError(Exception):
    pass

class DataIntegrityError(LispError):
    pass

class NotAListError(LispError):
    pass
class ParserError(LispError):
    pass
class InvalidExpressionError(ParserError):
    pass
class WrongNumberOfArgumentsError(InvalidExpressionError):
    pass
class UndefinedVariableError(InvalidExpressionError):
    pass

class LexicalParserError(ParserError):
    pass
class InvalidCharacterError(LexicalParserError):
    pass
class UnexpectedEndOfInputError(LexicalParserError):
    pass

class LexicalParser(object):
    def __init__(self, in_stream):
        if isinstance(in_stream, str):
            in_stream = StringIO(in_stream)
        if in_stream is not None:
            self.inStream = in_stream
        else:
            self.inStream = sys.stdin
        self.parserState = ParserState.Looking
        self.escapedState = None
        self.oneBack = None

    def getToken(self):
        token = self.readToken()
        if token == "":
            return None
        return token
                
    def isSymbolCharacter(self, c):
        # not whitespace and
        # not '\"{}[]:' and
        # not control character (< 32) and
        # not meta character (>128)
        return c in "!#$%&*+-./0123456789<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ^_`abcdefghijklmnopqrstuvwxyz|~"

    def readToken(self):
        token = ""
        while True:
            if self.parserState == ParserState.EOF:
                return token
            if self.oneBack != None:
                c = self.oneBack
                self.oneBack = None
            else:
                c = self.inStream.read(1)
            if len(c) == 0:
                # end of input, are we in the middle of something?
                if self.parserState == ParserState.InQuotedString:
                    raise UnexpectedEndOfInputError, "End of input in string"
                self.parserState = ParserState.EOF
                continue
            if self.parserState == ParserState.Looking:
                if c.isspace():
                    continue
                if c == ';':
                    self.inStream.readline()
                    continue
                if c == '\\':
                    self.escapedState = self.parserState
                    self.parserState = ParserState.InEscape
                    continue
                token += c
                if self.isSymbolCharacter(c):
                    self.parserState = ParserState.InSymbol
                    continue
                if c in "()'.":
                    return token
                if c == '"':
                    self.parserState = ParserState.InQuotedString
                    continue
                raise InvalidCharacterError, "Invalid character '%s'." % (c,)
            elif self.parserState == ParserState.InSymbol:
                if not self.isSymbolCharacter(c):
                    self.oneBack = c
                    self.parserState = ParserState.Looking
                    return token
                token += c
                continue
            elif self.parserState == ParserState.InEscape:
                token += c
                if self.escapedState == ParserState.Looking:
                    self.parserState = self.InSymbol
                else:
                    self.parserState = self.escapedState
                continue
            elif self.parserState == ParserState.InQuotedString:
                if c == '\\':
                    self.escapedState = self.parserState
                    self.parserState = ParserState.InEscape
                    continue
                token += c
                if c == '"':
                    self.parserState = ParserState.Looking
                    return token
                continue

if __name__ == "__main__":
    logging.basicConfig()
    logging.getLogger("lisp").setLevel(logging.WARNING)
    #logging.getLogger("lisp.interpreter").setLevel(logging.WARNING)
    #logging.getLogger("lisp.interpreter.mainloop").setLevel(logging.INFO)
    #logging.getLogger("lisp.interpreter.v").setLevel(logging.DEBUG)
    logging.getLogger("lisp.interpreter.v.trace").setLevel(logging.DEBUG)
    #logging.getLogger("lisp.interpreter.printout").setLevel(logging.DEBUG)
    #logging.getLogger("lisp.parser").setLevel(logging.DEBUG)
    #logging.getLogger("lisp.parser.lexical").setLevel(logging.INFO)
    #logging.getLogger("lisp.interpreter.v.bindlist").setLevel(logging.DEBUG)
    #logging.getLogger("lisp.interpreter.builtin").setLevel(logging.DEBUG)
    lisp = Interpreter()
    lisp.initialize()
    if len(sys.argv) != 2 or sys.argv[1] != '-n':
        lisp.interpret()

