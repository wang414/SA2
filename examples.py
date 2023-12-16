from z3 import *

all_consts = {}
target_param = []
const_calling = []
nonconst_calling = []
target_func = ''

def extract_calling(constraint) :
    if type(constraint) == list :
        if constraint[0] == target_func :
            for i in range(1, len(constraint)) :
                if type(constraint[i]) == str or type(constraint[i]) == list :
                    if constraint not in nonconst_calling :
                        nonconst_calling.append(constraint)
                    return
            if constraint not in const_calling :
                const_calling.append(constraint)
            return
        else :
            for i in range(1, len(constraint)) :
                extract_calling(constraint[i])
    return

class examp :
    def __init__(self, example) :
        self.consts = {}
        self.funcs = {'shr1' : 0, 'shr4' : 0, 'shr16' : 0, 'shl1' : 0, 'if0' : 0}
        self.constraints = []
        self.target_params = {}
        self.target_fun = example[len(example)-1]
        for func in example :
            if func != self.target_fun :
                if func.arity() == 0 :
                    if func.name() not in all_consts :
                        all_consts[func.name()] = example[func]
                    self.consts[func.name()] = example[func]
                else :
                    self.funcs[func.name()] = example[func]
        return
    
    def static_call(self, func, param) :
        if func == 'shr1' :
            return param[0] >> 1
        elif func == 'shr4' :
            return param[0] >> 4
        elif func == 'shr16' :
            return param[0] >> 16
        elif func == 'shl1' :
            return param[0] << 1
        elif func == 'if0' :
            if param[0] == 1 :
                return param[1]
            else :
                return param[2]
        else :
            print(func, param)
            assert False
    
    def call(self, expr) :
        if type(expr) == list :
            if expr[0] in self.funcs :
                para = []
                for term in expr[1:] :
                    para.append(self.call(term))
                return self.static_call(expr[0], para)
            elif expr[0] == '+' :
                return self.call(expr[1]) + self.call(expr[2])
            elif expr[0] == '-' :
                if len(expr) == 2 :
                    return - self.call(expr[1])
                else :
                    return self.call(expr[1]) - self.call(expr[2])
            elif expr[0] == 'ite' :
                if self.call(expr[1]) :
                    return self.call(expr[2])
                else :
                    return self.call(expr[3])
            elif expr[0] == '*' :
                return self.call(expr[1]) * self.call(expr[2])
            elif expr[0] == 'div' :
                temp = self.call(expr[2])
                if temp == 0 :
                    return 99999999999999999
                else :
                    return self.call(expr[1]) // temp
            elif expr[0] == 'mod' :
                temp = self.call(expr[2])
                if temp == 0 :
                    return 99999999999999999
                else :
                    return self.call(expr[1]) % temp
            elif expr[0] == '<=' :
                return self.call(expr[1]) <= self.call(expr[2])
            elif expr[0] == '>=' :
                return self.call(expr[1]) >= self.call(expr[2])
            elif expr[0] == '<' :
                return self.call(expr[1]) < self.call(expr[2])
            elif expr[0] == '>' :
                return self.call(expr[1]) > self.call(expr[2])
            elif expr[0] == '=' :
                return self.call(expr[1]) == self.call(expr[2])
            elif expr[0] == 'not' :
                return not self.call(expr[1])
            elif expr[0] == 'or' :
                return self.call(expr[1]) or self.call(expr[2])
            elif expr[0] == 'and' :
                return self.call(expr[1]) and self.call(expr[2])
            elif expr[0] == '=>' :
                return not self.call(expr[1]) or self.call(expr[2])
            elif expr[0] == 'bvnot' :
                return ~ self.call(expr[1])
            elif expr[0] == 'bvand' :
                return self.call(expr[1]) & self.call(expr[2])
            elif expr[0] == 'bvadd' :
                return self.call(expr[1]) + self.call(expr[2])
            elif expr[0] == 'bvor' :
                return self.call(expr[1]) | self.call(expr[2])
            elif expr[0] == 'bvxor' :
                return self.call(expr[1]) ^ self.call(expr[2])
            else :
                print(expr)
                assert False
        elif type(expr) == str :
            if expr in all_consts or expr in self.target_params :
                if expr in self.target_params :
                    return self.target_params[expr] 
                elif expr in self.consts :
                    temp = self.consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
                else :
                    temp = all_consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
            else :
                print(expr)
                assert False
        elif type(expr) == tuple :
            if expr[0] == 'Int' :
                return expr[1]
            elif type(expr[0]) == list :
                if expr[0][0] == 'BitVec' and expr[0][1] == ('Int', 64) :
                    return expr[1]
                else :
                    print(expr)
                    assert False
            else :
                print(expr)
                assert False
        else :
            print(expr)
            assert False
        return

    def eval(self, expr) :
        if type(expr) == list :
            if expr[0] in self.funcs :
                para = []
                for term in expr[1:] :
                    para.append(self.eval(term))
                return self.static_call(expr[0], para)
            elif expr[0] == target_func :
                for i in range(1, len(expr)) :
                    temp = self.eval(expr[i])
                    self.target_params[target_param[i-1]] = temp
                # print(self.call(self.value), self.value, self.target_params)
                return self.call(self.value)
            elif expr[0] == '+' :
                return self.eval(expr[1]) + self.eval(expr[2])
            elif expr[0] == '-' :
                if len(expr) == 2 :
                    return - self.eval(expr[1])
                else :
                    return self.eval(expr[1]) - self.eval(expr[2])
            elif expr[0] == 'ite' :
                if self.eval(expr[1]) :
                    return self.eval(expr[2])
                else :
                    return self.eval(expr[3])
            elif expr[0] == '*' :
                return self.eval(expr[1]) * self.eval(expr[2])
            elif expr[0] == 'div' :
                temp = self.eval(expr[2])
                if temp == 0 :
                    return 99999999999999999
                else :
                    return self.eval(expr[1]) // temp
            elif expr[0] == 'mod' :
                temp = self.eval(expr[2])
                if temp == 0 :
                    return 99999999999999999
                else :
                    return self.eval(expr[1]) % temp
            elif expr[0] == '<=' :
                return self.eval(expr[1]) <= self.eval(expr[2])
            elif expr[0] == '>=' :
                return self.eval(expr[1]) >= self.eval(expr[2])
            elif expr[0] == '<' :
                return self.eval(expr[1]) < self.eval(expr[2])
            elif expr[0] == '>' :
                return self.eval(expr[1]) > self.eval(expr[2])
            elif expr[0] == '=' :
                return self.eval(expr[1]) == self.eval(expr[2])
            elif expr[0] == 'not' :
                return not self.eval(expr[1])
            elif expr[0] == 'or' :
                return self.eval(expr[1]) or self.eval(expr[2])
            elif expr[0] == 'and' :
                return self.eval(expr[1]) and self.eval(expr[2])
            elif expr[0] == '=>' :
                return not self.eval(expr[1]) or self.eval(expr[2])
            elif expr[0] == 'bvnot' :
                return ~ self.eval(expr[1])
            elif expr[0] == 'bvand' :
                return self.eval(expr[1]) & self.eval(expr[2])
            elif expr[0] == 'bvadd' :
                return self.eval(expr[1]) + self.eval(expr[2])
            elif expr[0] == 'bvor' :
                return self.eval(expr[1]) | self.eval(expr[2])
            elif expr[0] == 'bvxor' :
                return self.eval(expr[1]) ^ self.eval(expr[2])
            else :
                print(expr)
                assert False
        elif type(expr) == str :
            if expr in all_consts :
                if expr in self.consts :
                    temp = self.consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    else : 
                        print(temp)
                        assert False
                else :
                    temp = all_consts[expr] 
                    if type(temp) == IntNumRef :
                        return temp.as_long()
                    elif type(temp) == int :
                        return temp
                    else : 
                        print(temp)
                        assert False
            else :
                print(expr)
                assert False
        elif type(expr) == tuple :
            if expr[0] == 'Int' :
                return expr[1]
            elif type(expr[0]) == list :
                if expr[0][0] == 'BitVec' and expr[0][1] == ('Int', 64) :
                    return expr[1]
                else :
                    print(expr)
                    assert False
            else :
                print(expr)
                assert False
        else :
            print(expr)
            assert False

    def check(self, expr, constraints) :
        # print(2, expr, self.consts)
        # print(target_func)
        self.value = expr
        # print(self.value)
        for constraint in constraints :
            # print(constraint)
            temp = self.eval(constraint)
            if not temp :
                return True
        return False

class examples :
    def __init__(self) :
        self.constraints = []
        self.examples = []
        return 

    def check(self, expr) :
        for exam in self.examples :
            if exam.check(expr, self.constraints) :
                return True
        return False

    def add_example(self, example) :
        self.examples.append(examp(example))
        return
    
    def add_constraint(self, constraint) :
        if len(constraint) == 2 :
            self.constraints.append(constraint[1])
            extract_calling(constraint[1])
        else :
            self.constraints.append(constraint[1:])
            extract_calling(constraint[1:])
        return
    
    def get_value(self, expr) :
        ret = []
        exam = examp([1])
        for calling in const_calling :
            # print(calling)
            for i in range(1, len(calling)) :
                exam.target_params[target_param[i-1]] = exam.eval(calling[i])
            ret.append(exam.call(expr))
        for example in self.examples :
            for calling in nonconst_calling :
                # print(calling)
                for i in range(1, len(calling)) :
                    temp = example.eval(calling[i])
                    exam.target_params[target_param[i-1]] = temp
                ret.append(exam.call(expr))
        return ret