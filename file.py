from os import close
from lark import Lark, exceptions
from lark.lexer import Token
from lark.tree import Tree
from lark.visitors import Interpreter, Visitor
import math

grammar = '''
start: program

?program: (statement ";")+

?statement: decl
    | assign
    | expr

?decl:  type ":" ID "=" expr -> vardecl
    | type ":" ID "(" funargsdecl ")" "{" return "}"  -> stfundecl
    | type ":" ID "(" funargsdecl ")" "{" program return "}"  -> tfundecl
    | "Void" ":" ID "(" funargsdecl ")" "{" program "}"  -> vfundecl

?funargsdecl: ((funargdecl ";")+ funargdecl | funargdecl?) -> funargsdecl

?funargdecl: type ":" ID -> funargdecl

?return: "return" opexpr ";" -> returnfun

?assign: ID "=" opexpr -> assignvar


?expr: "print" "(" opexpr ")" -> print
    | "if" "(" opexpr ")" "{" program "}" ("elif" "(" opexpr ")" "{" program "}")* ("else" "{" program "}")? -> ifexpr
    | "while" "(" opexpr ")" "{" program "}" -> whileexpr
    | "for" "(" decl ";" opexpr ";" assign ")" "{" program "}" -> forexpr
    | opexpr

?opexpr: opexpr EQOP opexpr -> eqexpr
    | opexpr COMPOP opexpr -> compexpr
    | opexpr ADDOP opexpr -> addexpr
    | opexpr MULOP opexpr -> mulexpr
    | opexpr "&&" opexpr -> andexpr
    | opexpr "||" opexpr -> orexpr
    | opexpr "mod" opexpr -> modexpr
    | opexpr "div" opexpr -> divexpr
    | "!" opexpr -> notexpr
    | "nroot" "(" opexpr ";" opexpr ")" -> rootexpr
    | "size" "(" opexpr ")" -> size
    | "toString" "(" opexpr ")" -> tostring
    | ID "(" funargs ")" -> runfun
    | opexpr2

?opexpr2: opexpr "[" opexpr "]" -> getentryexpr
    | opexpr "^" opexpr -> expexpr
    | atom

funargs: ((opexpr ";")+ opexpr | opexpr?) -> funargs

?atom: BOOLEAN -> bool
    | INT -> int
    | FLOAT -> float
    | ID -> var
    | STRING -> string
    | "-" atom -> negative
    | "(" opexpr ")"
    | "[" ((atom ";")+ atom | atom?) "]" -> list
    | "(" ((atom ";")* atom) ")" -> tuple



?type: TYPE -> type
    | type "[]" -> listtype
    | "(" ((type ";")* type) ")" -> tupletype

TYPE: "Int"
    | "Bool"
    | "Float"
    | "String"

ID: /[_a-zA-Z][_a-zA-Z0-9]*/
STRING: /\\\"[^\\\"]*\\\"/

BOOLEAN: "True" | "False"

ADDOP: "+" | "-"

MULOP: "*" | "/"

EQOP: "==" | "!="

COMPOP: ">=" | "<=" | "<" | ">"

INT: /[0-9]+/

FLOAT: /[0-9]+[.][0-9]+/


%import common.WS
%ignore WS
         '''

parser = Lark(grammar)

class Env:
    def __init__(self, o_env=None):
        self.n_varEnv = {}
        self.o_varEnv = {}
        self.n_funEnv = {}
        self.o_funEnv = {}
        if o_env != None:
           self.o_varEnv = o_env.o_varEnv.copy()
           self.o_varEnv.update(o_env.n_varEnv)
           self.o_funEnv = o_env.o_funEnv.copy()
           self.o_funEnv.update(o_env.n_funEnv)

    
    def update(self, i_env): 
        for (name, content) in i_env.o_varEnv.items():
            if (name in self.n_varEnv): self.n_varEnv[name] = content
            else: self.o_varEnv[name] = content

def isCompList(l, v):
    if isList(l) and isList(v):
        while isList(l) and isList(v):
            l = l[:-2]
            v = v[:-2]
        if v == "Void":
            return True
        elif checkType(l, v): return True
    return False

def isCompTuple(l, r):
    if isTuple(l) and isTuple(r):
        l = l[1:][:-1]
        r = r[1:][:-1]
        listl = l.split(";")
        listr = r.split(";")
        if len(listl) == len(listr):
            for i in range(len(listl)):
                if not checkType(listl[i], listr[i]): return False
            return True
    return False
            
def checkType(l,r):
    if l==r: return True
    if r=="Void": return True
    if l=="Float" and r=="Int": return True
    if isCompList(l,r): return True
    elif isCompTuple(l,r): return True
    else: return False

def isList(l):
    if (len(l) > 2 and l[-2:] == "[]"): return True
    else: return False

def isTuple(t):
    if (len(t) > 1 and t[0] == "(" and t[-1] == ")"): return True
    else: return False

def isFloat(t):
    if t == "Float" or t == "Int": return True
    else: return False

def editCompList(l, r):
    n = ""
    while isList(l) and isList(r):
        n += "[]"
        l = l[:-2]
        r = r[:-2]
    if r == "Void": return l + n
    elif l == "Void": return r + n
    elif (len(l) > 2 and l[-2:] == "[]") or (len(r) > 2 and r[-2:] == "[]"):
        raise Exception()
    else: return editType(l, r) + n

def editCompTuple(l, r):
    l = l[1:][:-1]
    r = r[1:][:-1]
    listl = l.split(";")
    listr = r.split(";")
    n = "("
    if len(listl) == len(listr):
        for i in range(len(listl)):
            n = n + editType(listl[i], listr[i]) + ";"
        return n[:-1] + ")"
    else: 
        raise Exception
            
def editType(l,r):
    if l==r: return l
    elif l == "Void": return r
    elif r == "Void": return l
    elif l == "Float" and r == "Int": return "Float"
    elif l == "Int" and r == "Float": return "Float"
    elif len(l) > 2 and len(r) > 2 and l[-2:] == "[]" and r[-2:] == "[]":
        n = editCompList(l, r)
        return n
    elif len(l) > 1 and len(r) > 1 and l[0] == "(" and r[0] == "(" and l[-1] == ")" and r[-1] == ")":
        n = editCompTuple(l, r)
        return n
    else: 
        raise Exception()
    


class TypeChecker(Interpreter): 
    def __init__(self, o_env = None):
        self.env = Env(o_env)
    
    def typeError(self, t1, t2):
        raise Exception("Type error: Expected %s, got %s" % (t1, t2))
    
    def addVar(self, name, value):
        self.env.n_varEnv[name] = value
    
    def getVar(self, name):
        if (name in self.env.n_varEnv): return self.env.n_varEnv[name]
        elif (name in self.env.o_varEnv): return self.env.o_varEnv[name]
        else: raise Exception("Variable not found: %s" % name)
    
    def addFun(self, name, args, body=None, r=None, type="Void"):
        self.env.n_funEnv[name] = (type, args, body, r)

    def getFun(self, name):
        if (name in self.env.n_funEnv): return self.env.n_funEnv[name]
        else: return self.env.o_funEnv[name]

    def int(self, tree):
        return "Int"
    
    def float(self, tree):
        return "Float"
    
    def bool(self, tree):
        return "Bool"
    
    def string(self, tree):
        return "String"
    
    def type(self, tree):
        type = tree.children[0]
        if type == "Bool": return "Bool"
        elif type == "Int": return "Int"
        elif type == "Float": return "Float"
        elif type == "String": return "String"
        else: raise Exception("Type not valid: %s" % type)
    
    def list(self, tree):
        contents = tree.children
        if len(contents) == 0: return "Void[]"
        else:
            type = self.visit(contents[0])
            for content in contents:
                value = self.visit(content)
                try:
                    type = editType(type, value)
                except: raise Exception("List can only have one type, but got: %s, %s" %(type, value))
                #if value != type: 
                #    if isCompList(value, type): type == value 
                #    elif not isCompList(type, value): raise Exception("List can only have one type, but got: %s, %s" %(type, value))
            return type + "[]"

    def listtype(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        return v + "[]"

    def tuple(self, tree):
        contents = tree.children
        values = "("
        for content in contents:
            value = self.visit(content)
            values = values + value + ";"
        if (values[-1] == ";"): values = values[:-1]
        return values + ")"
    
    def tupletype(self, tree):
        contents = tree.children
        values = "("
        for content in contents:
            value = self.visit(content)
            values = values + value + ";"
        if (values[-1] == ";"): values = values[:-1]
        return values + ")"
    
    def getentryexpr(self, tree):
        (e1, e2) = tree.children
        t = self.visit(e1)
        i = self.visit(e2)
        if not checkType("Int", i): self.typeError("Int", i)
        elif isList(t): return t[:-2]
        elif isTuple(t): return "Void" #
        elif t == "String": return "String"

    def negative(self, tree):
        value = tree.children[0]
        type = self.visit(value)
        if isFloat(type): return type
        else: self.typeError("Int or Float", type)
    
    def vardecl(self, tree):
        (type, name, e) = tree.children
        t = self.visit(type)
        v = self.visit(e)
        if checkType(t, v): self.addVar(name, t)
        #elif isCompList(t, v): self.addVar(name, t)
        else: self.typeError(t, v)
    
    def assignvar(self, tree):
        (name, e) = tree.children
        value = self.visit(e)
        type = self.getVar(name)
        if not checkType(type, value): self.typeError(type, value)
        #self.env.env[name] = self.visit(value)

    def var(self, tree):
        name = tree.children[0]
        return self.getVar(name)
        #try:
        #    return self.getVar(name)
        #    return self.env.env[name]
        #except KeyError:
        #    raise Exception("Variable not found: %s" % name)
    
    def vfundecl(self, tree):
        (name, args, body) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, body)
    
    def tfundecl(self, tree):
        (type, name, args, body, r) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, body, r, type)
    
    def stfundecl(self, tree):
        (type, name, args, r) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, None, r, type)
    
    def runfun(self, tree):
        (name, argsv) = tree.children
        (type, argslist, body, r) = self.getFun(name)
        argsvalues = self.visit(argsv)
        i_ev = TypeChecker(self.env)
        for i in range(len(argslist)):
            (argtype, argname) = argslist[i]
            argvalue = argsvalues[i]
            if not checkType(argtype, argvalue): self.typeError(argtype, argvalue)
            i_ev.addVar(argname, argvalue)
        if type != "Void":
            t = self.visit(type)
            if body != None:
                i_ev.visit(body)
            value = i_ev.visit(r)
            #if t != value:
            if not checkType(t, value):
                self.typeError(t, value)
            else:
                self.env.update(i_ev.env)
                return value
        else: 
            i_ev.visit(body)
            self.env.update(i_ev.env)

    def returnfun(self, tree):
        e = tree.children[0]
        return self.visit(e)

    def funargsdecl(self, tree):
        args = tree.children
        arglist = []
        for arg in args:
            (type, name) = self.visit(arg)
            arglist.append((type, name))
        return arglist
    
    def funargs(self, tree):
        args = tree.children
        arglist = []
        for arg in args:
            value = self.visit(arg)
            arglist.append(value)
        return arglist

    
    def addexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if v1 == "Int" and v3 == "Int": return "Int"
        elif isFloat(v1) and isFloat(v3): return "Float"
        if e2 == "+":
            if v1 == "String" and v3 == "String": return "String"
            elif isList(v1) and isList(v1): 
                try: return editType(v1, v3)
                except: raise Exception("'%s + %s' is not supported" %(v1, v3))
        else: raise Exception("'%s + %s' is not supported with %s" %(v1, v3, e2))
    
    def mulexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v3): self.typeError("Int or Float", v3)
        elif e2 == "/" or v1 == "Float" or v3 == "Float": return "Float"
        else: return "Int"
    
    def expexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v2): self.typeError("Int or Float", v2)
        else: return "Float"
    
    def rootexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v2): self.typeError("Int or Float", v2)
        else: return "Float"
    
    def modexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v2): self.typeError("Int or Float", v2)
        elif v1 == "Int" and v2 == "Int": return "Int"
        else: return "Float"
    
    def divexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v2): self.typeError("Int or Float", v2)
        else: return "Int"
    
    def eqexpr(self, tree):
        return "Bool"
    
    def compexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if not isFloat(v1): self.typeError("Int or Float", v1)
        elif not isFloat(v3): self.typeError("Int or Float", v3)
        return "Bool"

    def size(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        if isList(v) or isTuple(v) or v == "String": return "Int"
        raise Exception("Expected a list, tuple or String, but got %s" % v)
    
    def ifexpr(self, tree):
        exprs = tree.children
        i = 0
        lenght = len(exprs)-1
        while i<lenght:
            e1 = exprs[i]
            v1 = self.visit(e1)
            if v1 != "Bool": self.typeError("Bool", v1)
            else:
                e2 = exprs[i+1]
                i_ev = TypeChecker(self.env)
                i_ev.visit(e2)
                self.env.update(i_ev.env)
                i=i+2
        if (i == lenght):
            e = exprs[i]
            i_ev = TypeChecker(self.env)
            i_ev.visit(e)
            self.env.update(i_ev.env)
    
    def whileexpr(self, tree):
        (cond, e) = tree.children
        condType = self.visit(cond)
        if condType == "Bool":
            i_ev = TypeChecker(self.env)
            i_ev.visit(e)
            self.env.update(i_ev.env)
        else: self.typeError("Bool", condType)
    
    def forexpr(self, tree):
        (e1, e2, e3, e4) = tree.children
        i_ev = TypeChecker(self.env)
        i_ev.visit(e1)
        type = i_ev.visit(e2)
        if type == "Bool":
            ii_ev = TypeChecker(i_ev.env)
            ii_ev.visit(e4)
            i_ev.env.update(ii_ev.env)
            i_ev.visit(e3)
        self.env.update(i_ev.env)

    
    def notexpr(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        if v == "Bool": return "Bool"
        else: self.typeError("Bool", v)
    
    def andexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if v1 != "Bool": self.typeError("Bool", v1)
        elif v2 != "Bool": self.typeError("Bool", v2)
        return "Bool"

    def orexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if v1 != "Bool": self.typeError("Bool", v1)
        elif v2 != "Bool": self.typeError("Bool", v2)
        return "Bool"
    
    def tostring(self, tree):
        self.visit(tree.children[0])
        return "String"
    
    def print(self, tree):
        self.visit(tree.children[0])





class Evaluator(Interpreter): 
    def __init__(self, o_env = None):
        self.env = Env(o_env)
    
    def addVar(self, name, value):
        self.env.n_varEnv[name] = value

    def updateVar(self, name, value):
        if (name in self.env.n_varEnv): self.env.n_varEnv[name] = value
        else: self.env.o_varEnv[name] = value
    
    def getVar(self, name):
        if (name in self.env.n_varEnv): return self.env.n_varEnv[name]
        else: return self.env.o_varEnv[name]
    
    def addFun(self, name, args, body=None, r=None, type="Void"):
        self.env.n_funEnv[name] = (type, args, body, r)

    def getFun(self, name):
        if (name in self.env.n_funEnv): return self.env.n_funEnv[name]
        else: return self.env.o_funEnv[name]
    
    def list(self, tree):
        contents = tree.children
        values = []
        for content in contents:
            value = self.visit(content)
            values.append(value)
        return values
    
    def tuple(self, tree):
        contents = tree.children
        values = []
        for content in contents:
            value = self.visit(content)
            values.append(value)
        return tuple(values)
    
    def getentryexpr(self, tree):
        (e1, e2) = tree.children
        i = self.visit(e2)
        list = self.visit(e1)
        if (i < len(list) and i >= 0) or (i >= -len(list) and i < 0): 
            if isinstance(list, str): return str(list[i])
            else: return list[i]
        else: raise Exception("%s is out of bounds: %s" %(i, list))

    def int(self, tree):
        value = tree.children[0]
        return int(value)
    
    def float(self, tree):
        value = tree.children[0]
        return float(value)
    
    def string(self, tree):
        value = tree.children[0]
        return str(value).strip("\"")
    
    def bool(self, tree):
        value = tree.children[0]
        if value == "True": return "True"
        else: return "False"

    def negative(self, tree):
        value = tree.children[0]
        return -1 * self.visit(value)
    
    def vardecl(self, tree):
        (type, name, value) = tree.children
        self.addVar(name, self.visit(value))
        #self.env.env[name] = self.visit(value)
    
    def assignvar(self, tree):
        (name, value) = tree.children
        self.updateVar(name, self.visit(value))
        #self.env.env[name] = self.visit(value)

    def var(self, tree):
        name = tree.children[0]
        return self.getVar(name)
        #try:
        #    return self.getVar(name)
        #    return self.env.env[name]
        #except KeyError:
        #    raise Exception("Variable not found: %s" % name)
    
    def vfundecl(self, tree):
        (name, args, body) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, body)
    
    def tfundecl(self, tree):
        (type, name, args, body, r) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, body, r, type)
    
    def stfundecl(self, tree):
        (type, name, args, r) = tree.children
        argslist = self.visit(args)
        self.addFun(name, argslist, None, r, type)
    
    def runfun(self, tree):
        (name, argsv) = tree.children
        (type, argslist, body, r) = self.getFun(name)
        argsvalues = self.visit(argsv)
        i_ev = Evaluator(self.env)
        for i in range(len(argslist)):
            (argtype, argname) = argslist[i]
            argvalue = argsvalues[i]
            i_ev.addVar(argname, argvalue)
        if type != "Void":
            if body != None:
                i_ev.visit(body)
            value = i_ev.visit(r)
            self.env.update(i_ev.env)
            return value
        i_ev.visit(body)
        self.env.update(i_ev.env)

    def returnfun(self, tree):
        e = tree.children[0]
        return self.visit(e)

    def funargsdecl(self, tree):
        args = tree.children
        arglist = []
        for arg in args:
            (type, name) = self.visit(arg)
            arglist.append((type, name))
        return arglist
    
    def funargs(self, tree):
        args = tree.children
        arglist = []
        for arg in args:
            value = self.visit(arg)
            arglist.append(value)
        return arglist

    
    def addexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if (e2 == '+'):
            return v1 + v3
        return v1 - v3
    
    def mulexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if (e2 == '*'):
            return v1 * v3
        return v1 / v3
    
    def expexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        return v1**v2
    
    def rootexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        return v1**(1/v2)
    
    def divexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        return int(v1//v2)
    
    def modexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        return v1%v2
    
    def eqexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if (e2 == "=="):
            if (v1 == v3): return "True"
            else: return "False"
        else:
            if (v1 == v3): return "False"
            else: return "True"
        
    def compexpr(self, tree):
        (e1, e2, e3) = tree.children
        v1 = self.visit(e1)
        v3 = self.visit(e3)
        if (e2 == ">="):
            if (v1 >= v3): return "True"
            else: return "False"
        elif (e2 == "<="):
            if (v1 <= v3): return "True"
            else: return "False"
        elif (e2 == "<"):
            if (v1 < v3): return "True"
            else: return "False"
        else:
            if (v1 > v3): return "True"
            else: return "False"
        
    def size(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        return len(v)
    
    def ifexpr(self, tree):
        exprs = tree.children
        i = 0
        lenght = len(exprs)-1
        while i<lenght:
            e1 = exprs[i]
            v1 = self.visit(e1)
            if (v1 == "True"):
                e2 = exprs[i+1]
                i_ev = Evaluator(self.env)
                i_ev.visit(e2)
                self.env.update(i_ev.env)
                i = lenght+1
            else: i=i+2
        if (i == lenght):
            e = exprs[i]
            i_ev = Evaluator(self.env)
            i_ev.visit(e)
            self.env.update(i_ev.env)
    
    def whileexpr(self, tree):
        (cond, e) = tree.children
        while self.visit(cond) == "True":
            i_ev = Evaluator(self.env)
            i_ev.visit(e)
            self.env.update(i_ev.env)
    
    def forexpr(self, tree):
        (e1, e2, e3, e4) = tree.children
        i_ev = Evaluator(self.env)
        i_ev.visit(e1)
        while i_ev.visit(e2) == "True":
            ii_ev = Evaluator(i_ev.env)
            ii_ev.visit(e4)
            i_ev.env.update(ii_ev.env)
            i_ev.visit(e3)
        self.env.update(i_ev.env)

    
    def notexpr(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        if v == "False": return "True"
        elif v == "True": return "False"
        else: raise Exception("Value is not a BOOLEAN: %s" % v)
    
    def andexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if (v1 == "True") and (v2 == "True"): return "True"
        elif (v1 != "True") and (v1 != "False") : raise Exception("Value is not a BOOLEAN: %s" % v1)
        elif (v2 != "True") and (v2 != "False") : raise Exception("Value is not a BOOLEAN: %s" % v2)
        else: return "False"

    def orexpr(self, tree):
        (e1, e2) = tree.children
        v1 = self.visit(e1)
        v2 = self.visit(e2)
        if (v1 == "False") and (v2 == "False"): return "False"
        elif (v1 != "True") and (v1 != "False") : raise Exception("Value is not a BOOLEAN: %s" % v1)
        elif (v2 != "True") and (v2 != "False") : raise Exception("Value is not a BOOLEAN: %s" % v2)
        else: return "True"
    
    def tostring(self, tree):
        e = tree.children[0]
        v = self.visit(e)
        return str(v)

    def print(self, tree):
        value = self.visit(tree.children[0])
        print(value)


def runCode(code, tc, ev):
    tree = parser.parse(code)
    #tc.visit(tree)
    ev.visit(tree)

def execute(path, o_tc = TypeChecker(), o_ev = Evaluator()):
    with open(path, "r") as file:
        code = file.read()
        close
    i_tc = TypeChecker(o_tc.env)
    i_ev = Evaluator(o_ev.env)
    runCode(code, i_tc, i_ev)
    #o_tc.env.update(i_tc.env)
    o_ev.env.update(i_ev.env)

if __name__ == '__main__':
    tc = TypeChecker()
    ev = Evaluator()
    while True:
        code = input('> ')
        if code.strip() == "quit()":
            break
        try:
            runCode(code, tc, ev)
        except Exception as e:
            print(e)