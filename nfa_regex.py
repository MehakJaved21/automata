
# Note: you will not need to change anything in this file.
#       It is highly recommended you peruse the Regex classes below, however.


# A top-down parser for regular expressions; we'll learn about these later ;)
def regex(s):
    """basic top-down str->Regex parser"""
    symb = "()|*"
    alpha = "0123456789zusaftoigvbqnlrkjhxcmdeywp"
    for c in s:
        if (symb+alpha).find(c) == -1: return EpsilonRegex()
    def peek(s):
        if s == "": return None;
        if s[0] == " ": return peek(s[1:])
        else: return s[0]
    def pop(s):
        if s == "": return None;
        if s[0] == " ": return pop(s[1:])
        else: return s[1:]
    def disj(s):
        (a,s0) = juxt(s)
        if peek(s0) == "|":
            (b,s1) = disj(pop(s0))
            return (DisjRegex(a,b), s1)
        else:
            return (a,s0)
    def juxt(s): 
        (a,s0) = star(s)
        if peek(s0) != None and peek(s0) != ")" and peek(s0) != "|":
            (b,s1) = juxt(s0)
            return (SeqRegex(a,b), s1)
        else:
            return (a,s0)
    def star(s): 
        (a,s0) = paren(s)
        while peek(s0) == "*" and peek(pop(s0)) == "*": s0 = pop(s0)
        if peek(s0) == "*":
            return (StarRegex(a), pop(s0))
        else:
            return (a,s0)
    def paren(s):
        if peek(s) == "(":
            (a,s0) = disj(pop(s))
            if peek(s0) != ")": print("Badly matched Parens!"); return EpsilonRegex()
            return (a,pop(s0))
        elif peek(s) != None and alpha.find(peek(s)) >= 0:
            return (CharRegex(peek(s)), pop(s))
        else:
            return (EpsilonRegex(), s)
    (r,s0) = disj(s)
    return r



# A base class for regular expressions   
class Regex:
    """A base class for Regular expressions"""
    pass


# An epsilon regular expression
class EpsilonRegex(Regex):
    """A class for the language {""}, i.e., of just the empty string"""
    pass

    def __str__(self):
        return "ε"

    
# A single-character regex
class CharRegex(Regex):
    """A class for single-letter, x, regular expressions"""
    
    def __init__(self, letter):
        if isinstance(letter, str) and len(letter) == 1:
            self.x = letter
        else:
            raise "CharRegex must be instantiated with a length-1 string."

    def __str__(self):
        return str(self.x)
        

# A kleene star, derived regex
class StarRegex(Regex):
    """A class for the kleene-closure of a single component Regex"""
    
    def __init__(self, r):
        if isinstance(r, Regex):
            self.r0 = r
        else:
            raise "StarRegex must be instantiated with a single component Regex."

    def __str__(self):
        r0 = str(self.r0)
        if len(r0) == 1 or (r0[0] == "(" and r0[-1] == ")"):
            return r0+"*"
        else:
            return "("+r0+")*"

        
# A disjunction, derived regex
class DisjRegex(Regex):
    """A class for the disjunction of two component Regexes"""
    
    def __init__(self, r0, r1):
        if isinstance(r0, Regex) and isinstance(r1, Regex):
            self.r0 = r0
            self.r1 = r1
        else:
            raise "DisjRegex must be instantiated with two component Regexes."

    def __str__(self):
        r0 = str(self.r0)
        r1 = str(self.r1)
        return r0 + "|" + r1

    
# A sequence, derived regex
class SeqRegex(Regex):
    """A class for a sequence of two component Regexes"""
    
    def __init__(self, r0, r1):
        if isinstance(r0, Regex) and isinstance(r1, Regex):
            self.r0 = r0
            self.r1 = r1
        else:
            raise "SeqRegex must be instantiated with two component Regexes."

    def __str__(self):
        r0 = str(self.r0)
        r1 = str(self.r1)
        if isinstance(self.r0, DisjRegex):
            r0 = "(" + r0 + ")"
        if isinstance(self.r1, DisjRegex):
            r1 = "(" + r1 + ")"
        return r0+r1
        

        
