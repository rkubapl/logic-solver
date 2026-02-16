import copy
from enum import Enum

class color:
   PURPLE = '\033[95m'
   CYAN = '\033[96m'
   DARKCYAN = '\033[36m'
   BLUE = '\033[94m'
   GREEN = '\033[92m'
   YELLOW = '\033[93m'
   RED = '\033[91m'
   BOLD = '\033[1m'
   UNDERLINE = '\033[4m'
   END = '\033[0m'

class Type(Enum):
    TERM = 1
    UNARY = 2
    BINARY = 3

operators = {
    "I": {"weight": 6, "type": Type.BINARY, "print_as": "⇒"},
    "|": {"weight": 5, "type": Type.BINARY, "print_as": "∨"},
    "&": {"weight": 4, "type": Type.BINARY, "print_as": "∧"},
    "!": {"weight": 3, "type": Type.UNARY, "print_as": "¬"}
}

class Expression:
    def __init__(self, left, right, operator, type):
        self.left = left
        self.right = right
        self.operator = operator
        self.type = type
        self.applied = False #highlight to which expression was applied a rule

    def set_applied(self, applied):
        self.applied = applied

    def to_string(self, color_apply = True):
        symbol_string = operators[self.operator]["print_as"] if self.operator is not None else ""
        res = ""
        if self.type == Type.BINARY:
            res = "(" + self.left.to_string(False) + " " + symbol_string + " " + self.right.to_string(False) + ")"
        elif self.type == Type.UNARY:
            res = symbol_string + self.right.to_string(False)
        else:
            res = self.right

        if self.applied and color_apply:
            return color.RED + res + color.END
        else:
            return res

class Sequent:
    def __init__(self, ant, con):
        self.ant = ant #antecedents (assumptions)
        self.con = con #consequents (propositions)
        self.check_if_axiom()

    def check_if_axiom(self):
        ant_terms = {expr.right for expr in self.ant if expr.type == Type.TERM}
        con_terms = {expr.right for expr in self.con if expr.type == Type.TERM}

        # p,q |- p,r
        if len(ant_terms & con_terms) > 0:
            self.axiom = True
            return

        #F, p |- q
        if "F" in ant_terms:
            self.axiom = True
            return

        self.axiom = False

    def to_string(self):
        res = ""
        if self.axiom:
            res += "(AXIOM) "
        if len(self.ant) > 0:
            res += ", ".join([exp.to_string() for exp in self.ant]) + " "
        res += "⊢"
        if len(self.con) > 0:
            res += " " + ", ".join([exp.to_string() for exp in self.con])
        return res


def parse(text: str):
    #https://github.com/PranayB003/gentzen/blob/main/parse.go
    if len(text) == 1:
        return Expression(None, text, None, Type.TERM)

    level = [0 for _ in range(len(text))]

    cur_level = 0
    for i, char in enumerate(text):
        if char == "(":
            cur_level += 1
            level[i] = cur_level
        elif char == ")":
            level[i] = cur_level
            cur_level -= 1
        else:
            level[i] = cur_level

    if cur_level != 0:
        raise SyntaxError("Unbalanced parenthesis")

    #remove redundant parentheses
    #check for situation like ((a&b)I(a|b))
    while 0 not in level:
        text = text[1:-1]
        level = [val-1 for val in level[1:-1]]

    op, pos = -1, 0

    for i, ch in enumerate(text):
        if ch in ["(", ")"] or level[i] != 0:
            continue

        cur_op = operators[ch]["weight"] if ch in operators.keys() else -1

        if cur_op == -1:
            continue

        if cur_op > op:
            op = cur_op
            pos = i

    op_type = operators[text[pos]]["type"]

    if op_type == Type.BINARY:
        expr = Expression(parse(text[:pos]), parse(text[pos + 1:]), text[pos], op_type)
        return expr

    if op_type == Type.UNARY:
        return Expression(None, parse(text[pos + 1:]), text[pos], op_type)

    return None

#output stores resulting sequents after applying rule depending on side of a sequent and operator
#Binary operator: A [binary operator] B
#Unary operator: [unary operator]B
#ant |- con

ant_rules = {
    "I": {"output": [{"con": ["A"]},{"ant": ["B"]}]},
    "&": {"output": [{"ant": ["A", "B"]}]},
    "|": {"output": [{"ant": ["A"]},{"ant": ["B"]}]},
    "!": {"output": [{"con": ["B"]}]}
}

con_rules = {
    "I": {"output": [{"ant": ["A"], "con": ["B"]}]},
    "&": {"output": [{"con": ["A"]},{"con": ["B"]}]},
    "|": {"output": [{"con": ["A", "B"]}]},
    "!": {"output": [{"ant": ["B"]}]}
}

def apply_rule(seq: Sequent, expr: Expression, rule) -> list[Sequent]:
    res_seqs = []
    for output in rule["output"]:
        new_seq = copy.deepcopy(seq)
        loc = {"ant": new_seq.ant, "con": new_seq.con}
        for k, v in output.items():
            for val in v:
                loc[k].append(expr.left if val == "A" else expr.right)
        new_seq.check_if_axiom()
        res_seqs.append(new_seq)
    return res_seqs

def continue_proof(seq: Sequent) -> tuple[str, list[Sequent]]:
    #first iteration - look for rules which gives one output
    #second iteration - take everything which isn't term
    for only_one_output in [True, False]:
        j = 0
        for expressions, rules in [[seq.ant, ant_rules], [seq.con, con_rules]]:
            for i, expr in enumerate(expressions):
                if expr.type == Type.TERM:
                    continue

                rule = rules[expr.operator]

                if only_one_output and len(rule["output"]) != 1:
                    continue

                #found rule
                expr.applied = True
                old_seq = seq.to_string() + f" ({operators[expr.operator]['print_as']} {['L', 'R'][j]})"

                cur_expr = expressions.pop(i)
                return old_seq, apply_rule(seq, cur_expr, rule)
            j += 1
    return "", [] #empty array means there is no expression in sequent and sequent isn't axiom, which means proof is unsuccessful

#Example: (pI(qIr))|-(qI(pIr))
input_str = input("> ")

str_split = input_str.replace(" ", "").split("|-")

if len(str_split) == 1:
    left_str, right_str = None, str_split[0]
elif len(str_split) == 2:
    left_str, right_str = str_split[0], str_split[1]
else:
    raise Exception("Invalid input")

left = [parse(expr) for expr in left_str.split(",")] if left_str else []
right = [parse(expr) for expr in right_str.split(",")] if right_str else []

sequents = [Sequent(left, right)]
frames = []

while True:
    res_sequents: list[Sequent] = [] #resulting sequents after applying rule to each
    old_seqs: list[str] = [] #sequents before applying rules with highlighted expression

    for seq in sequents:
        if seq.axiom: #if sequent is axiom, exclude it from next frames
            old_seqs.append(seq.to_string())
            continue

        old_seq, new_seqs = continue_proof(seq)
        if len(new_seqs) == 0:
            print("Proof unsuccessful")
            exit(0)

        res_sequents.extend(new_seqs)
        old_seqs.append(old_seq)

    frames.append("        ".join(old_seqs))
    sequents = res_sequents

    all_axioms = sum([1 for seq in res_sequents if seq.axiom])
    if all_axioms == len(res_sequents):
        break


frames.append("        ".join([seq.to_string() for seq in sequents]))
frames.reverse()

for i, frame in enumerate(frames):
    print(color.UNDERLINE + f"FRAME {len(frames)-i}" + color.END)
    print(frame)