"""Лаборатори 5: үндсэн даалгаврын 1-8-р алхам.

Зөвхөн Python standard library шаардлагатай. Ажиллуулах: python Lab5_Logic.py
Тоолуур бүр хайлт эхлэхэд тэглэгдэнэ. None нь хязгаарт хүрсэн, False нь
дууссан хайлтын сөрөг хариу. DPLL-ийн хоосон dict нь мөн зөв SAT загвар.
"""

from itertools import product, combinations
from functools import reduce
from pathlib import Path
import json
import platform
import random
import sys

MODEL_LIMIT = 200_000
RESOLVENT_LIMIT = 100_000


def Sym(n):
    return ('sym', n)


def Not(a):
    return ('not', a)


def And(a, b):
    return ('and', a, b)


def Or(a, b):
    return ('or', a, b)


def Imp(a, b):
    return ('imp', a, b)


def Iff(a, b):
    return ('iff', a, b)


def symbols(s):
    if s[0] == 'sym':
        return {s[1]}
    if s[0] == 'not':
        return symbols(s[1])
    return symbols(s[1]) | symbols(s[2])


def to_str(s):
    if s[0] == 'sym':
        return s[1]
    if s[0] == 'not':
        return f'~{to_str(s[1])}'
    sign = {'and': '&', 'or': '|', 'imp': '=>', 'iff': '<=>'}[s[0]]
    return f'({to_str(s[1])} {sign} {to_str(s[2])})'


def conjoin(sentences):
    """Нэг буюу олон өгүүлбэрийг And-аар нэгтгэнэ."""
    sentences = list(sentences)
    if not sentences:
        raise ValueError('Өгүүлбэрийн жагсаалт хоосон байна')
    return reduce(And, sentences)


def pl_true(s, model):
    op = s[0]
    if op == 'sym':
        return model[s[1]]
    if op == 'not':
        return not pl_true(s[1], model)
    a, b = pl_true(s[1], model), pl_true(s[2], model)
    if op == 'and':
        return a and b
    if op == 'or':
        return a or b
    if op == 'imp':
        return (not a) or b
    if op == 'iff':
        return a == b
    raise ValueError(f'Танигдаагүй холбоос: {op}')


def all_models(syms):
    names = sorted(syms)
    for values in product((False, True), repeat=len(names)):
        yield dict(zip(names, values))


def tt_entails(kb, alpha, limit=None):
    checked = 0
    for model in all_models(symbols(kb) | symbols(alpha)):
        checked += 1
        if limit is not None and checked > limit:
            return None, checked
        if pl_true(kb, model) and not pl_true(alpha, model):
            return False, checked
    return True, checked


def is_valid(s):
    return all(pl_true(s, m) for m in all_models(symbols(s)))


def is_satisfiable(s):
    return any(pl_true(s, m) for m in all_models(symbols(s)))


def print_truth_table(s):
    names = sorted(symbols(s))
    print(' '.join(names) + ' | ' + to_str(s))
    for model in all_models(names):
        print(' '.join('T' if model[n] else 'F' for n in names),
              '|', 'T' if pl_true(s, model) else 'F')


def eliminate_iff(s):
    if s[0] == 'sym':
        return s
    if s[0] == 'not':
        return Not(eliminate_iff(s[1]))
    a, b = eliminate_iff(s[1]), eliminate_iff(s[2])
    if s[0] == 'iff':
        return And(Imp(a, b), Imp(b, a))
    return (s[0], a, b)


def eliminate_imp(s):
    if s[0] == 'sym':
        return s
    if s[0] == 'not':
        return Not(eliminate_imp(s[1]))
    a, b = eliminate_imp(s[1]), eliminate_imp(s[2])
    if s[0] == 'imp':
        return Or(Not(a), b)
    return (s[0], a, b)


def push_not(s):
    op = s[0]
    if op == 'sym':
        return s
    if op == 'not':
        a = s[1]
        if a[0] == 'sym':
            return s
        if a[0] == 'not':
            return push_not(a[1])
        if a[0] == 'and':
            return Or(push_not(Not(a[1])), push_not(Not(a[2])))
        if a[0] == 'or':
            return And(push_not(Not(a[1])), push_not(Not(a[2])))
        raise ValueError('Эхлээд iff, imp холбоосыг арилгана')
    return (op, push_not(s[1]), push_not(s[2]))


def distribute(s):
    if s[0] in ('sym', 'not'):
        return s
    a, b = distribute(s[1]), distribute(s[2])
    if s[0] == 'and':
        return And(a, b)
    if a[0] == 'and':
        return And(distribute(Or(a[1], b)), distribute(Or(a[2], b)))
    if b[0] == 'and':
        return And(distribute(Or(a, b[1])), distribute(Or(a, b[2])))
    return Or(a, b)


def to_cnf(s):
    return distribute(push_not(eliminate_imp(eliminate_iff(s))))


def negate_literal(lit):
    return lit[1:] if lit.startswith('~') else '~' + lit


def literal_name(lit):
    return lit[1:] if lit.startswith('~') else lit


def is_tautology_clause(clause):
    return any(negate_literal(lit) in clause for lit in clause)


def clause_key(clause):
    return len(clause), tuple(sorted(clause))


def normalize_clauses(clauses):
    return {frozenset(c) for c in clauses if not is_tautology_clause(c)}


def to_clauses(s):
    cnf = to_cnf(s)

    def literals(node):
        if node[0] == 'or':
            return literals(node[1]) | literals(node[2])
        if node[0] == 'sym':
            return {node[1]}
        if node[0] == 'not' and node[1][0] == 'sym':
            return {'~' + node[1][1]}
        raise ValueError('CNF дотор литерал бус бүтэц байна')

    def clauses(node):
        if node[0] == 'and':
            return clauses(node[1]) | clauses(node[2])
        clause = frozenset(literals(node))
        return set() if is_tautology_clause(clause) else {clause}

    return clauses(cnf)


def clause_symbols(clauses):
    return {literal_name(lit) for c in clauses for lit in c}


def literal_value(lit, model):
    name = literal_name(lit)
    if name not in model:
        return None
    return not model[name] if lit.startswith('~') else model[name]


def clause_value(clause, model):
    """True: хангагдсан, False: зөрчил, None: оноолт дутуу."""
    undecided = False
    for lit in clause:
        value = literal_value(lit, model)
        if value is True:
            return True
        if value is None:
            undecided = True
    return None if undecided else False


def tt_satisfiable_clauses(clauses, limit=None):
    clauses = sorted(normalize_clauses(clauses), key=clause_key)
    checked = 0
    for model in all_models(clause_symbols(clauses)):
        checked += 1
        if limit is not None and checked > limit:
            return None, checked
        if all(clause_value(c, model) is True for c in clauses):
            return True, checked
    return False, checked


def resolve(ci, cj):
    results = []
    for lit in sorted(ci):
        opposite = negate_literal(lit)
        if opposite in cj:
            resolvent = frozenset((ci - {lit}) | (cj - {opposite}))
            if not is_tautology_clause(resolvent):
                results.append(resolvent)
    return results


def resolution_unsat(clauses, limit=None):
    """(UNSAT эсэх, resolvent тоо). Бүх хосыг тойрог бүрд шалгана.

    Тоолуурт tautology биш үүссэн resolvent бүр орно, өмнө байсан эсэхээс
    үл хамаарна. Үгүйсгэлийн нэг хосыг л арилгана. Хоосон set of clauses
    нь True CNF, харин хоосон frozenset clause нь False CNF байна.
    """
    known = normalize_clauses(clauses)
    generated = 0
    if frozenset() in known:
        return True, generated
    while True:
        new = set()
        ordered = sorted(known, key=clause_key)
        for ci, cj in combinations(ordered, 2):
            for resolvent in resolve(ci, cj):
                generated += 1
                if limit is not None and generated > limit:
                    return None, generated
                if not resolvent:
                    return True, generated
                new.add(resolvent)
        if new <= known:
            return False, generated
        known |= new


def pl_resolution(kb_clauses, alpha, limit=None, stats=None):
    """KB ⊨ alpha эсэхийг True/False-оор буцаана; stats-д тоолуур хадгална."""
    result, generated = resolution_unsat(set(kb_clauses) | to_clauses(Not(alpha)), limit)
    if stats is not None:
        stats.clear()
        stats['resolvents'] = generated
    return result


def find_pure_symbol(symbols, clauses, model):
    active = [c for c in clauses if clause_value(c, model) is not True]
    for name in sorted(symbols):
        positive = any(name in c for c in active)
        negative = any('~' + name in c for c in active)
        if positive and not negative:
            return name, True
        if negative and not positive:
            return name, False
    return None


def find_unit_clause(clauses, model):
    for clause in sorted(clauses, key=clause_key):
        if clause_value(clause, model) is True:
            continue
        remaining = [lit for lit in clause if literal_name(lit) not in model]
        if len(remaining) == 1:
            lit = remaining[0]
            return literal_name(lit), not lit.startswith('~')
    return None


def dpll(clauses, symbols, model, stats=None):
    if stats is None:
        stats = {'calls': 0}
    stats['calls'] = stats.get('calls', 0) + 1
    active = []
    for clause in clauses:
        value = clause_value(clause, model)
        if value is False:
            return False
        if value is not True:
            active.append(clause)
    if not active:
        return dict(model)

    choice = find_pure_symbol(symbols, active, model)
    if choice is None:
        choice = find_unit_clause(active, model)
    if choice is not None:
        name, value = choice
        return dpll(active, symbols - {name}, {**model, name: value}, stats)

    name = sorted(symbols)[0]
    for value in (True, False):
        result = dpll(active, symbols - {name}, {**model, name: value}, stats)
        if result is not False:
            return result
    return False


def dpll_satisfiable(clauses, stats=None):
    if stats is None:
        stats = {}
    stats.clear()
    stats['calls'] = 0
    clauses = normalize_clauses(clauses)
    names = clause_symbols(clauses)
    result = dpll(clauses, names, {}, stats)
    if result is False:
        return False
    return {name: result.get(name, False) for name in sorted(names)}


def wumpus_problem():
    P11, P12, P21, P22, P31 = map(Sym, ('P11', 'P12', 'P21', 'P22', 'P31'))
    B11, B21 = map(Sym, ('B11', 'B21'))
    rules = [Not(P11), Iff(B11, Or(P12, P21)),
             Iff(B21, Or(P11, Or(P22, P31))), Not(B11), B21]
    queries = [Not(P12), Not(P21), Not(P22), Not(P31), Or(P22, P31)]
    return conjoin(rules), queries


def solve_wumpus():
    kb, queries = wumpus_problem()
    kb_clauses = to_clauses(kb)
    models = [m for m in all_models(symbols(kb)) if pl_true(kb, m)]
    rows = []
    for query in queries:
        tt, tt_count = tt_entails(kb, query)
        res_stats = {}
        resolution = pl_resolution(kb_clauses, query, stats=res_stats)
        res_count = res_stats['resolvents']
        stats = {}
        countermodel = dpll_satisfiable(kb_clauses | to_clauses(Not(query)), stats)
        dpll_entails = countermodel is False
        assert tt == resolution == dpll_entails
        if countermodel is not False:
            assert pl_true(kb, countermodel) and not pl_true(query, countermodel)
        rows.append({'query': to_str(query), 'entails': tt,
                     'tt_models': tt_count, 'resolvents': res_count,
                     'dpll_calls': stats['calls'], 'countermodel': countermodel})
    assert len(models) == 3
    assert [r['entails'] for r in rows] == [True, True, False, False, True]
    return {'models': models, 'model_count': len(models), 'queries': rows,
            'clauses': [sorted(c) for c in sorted(kb_clauses, key=clause_key)]}


def random_3sat(n, m, seed):
    if n < 3 or m < 0:
        raise ValueError('n >= 3, m >= 0 байна')
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        names = rng.sample(range(1, n + 1), 3)
        literals = [f'X{i}' if rng.choice((True, False)) else f'~X{i}' for i in names]
        clauses.append(frozenset(literals))
    return clauses


def run_benchmarks(wumpus=None):
    if wumpus is None:
        wumpus = solve_wumpus()
    rows = []
    for index in (0, 2, 4):
        item = wumpus['queries'][index]
        rows.append({'problem': 'Wumpus: ' + item['query'], 'task': 'entailment',
                     'result': item['entails'], 'tt_result': item['entails'],
                     'res_result': item['entails'], 'dpll_result': item['entails'],
                     'tt_models': item['tt_models'], 'resolvents': item['resolvents'],
                     'dpll_calls': item['dpll_calls']})
    for n in (10, 15, 20):
        clauses = random_3sat(n, 4*n, seed=1)
        assert len(clauses) == 4*n and all(len(c) == 3 for c in clauses)
        tt, tt_count = tt_satisfiable_clauses(clauses, MODEL_LIMIT)
        unsat, res_count = resolution_unsat(clauses, RESOLVENT_LIMIT)
        resolution_sat = None if unsat is None else not unsat
        stats = {}
        model = dpll_satisfiable(clauses, stats)
        sat = model is not False
        if sat:
            assert all(clause_value(c, model) is True for c in clauses)
        assert tt is None or tt == sat
        assert resolution_sat is None or resolution_sat == sat
        rows.append({'problem': f'3-SAT, n={n}, m={4*n}', 'task': 'satisfiability',
                     'result': sat, 'tt_result': tt, 'res_result': resolution_sat,
                     'dpll_result': sat, 'tt_models': tt_count,
                     'resolvents': res_count, 'dpll_calls': stats['calls'],
                     'model': model, 'distinct_clauses': len(set(clauses))})
    return rows


def verify_required_steps():
    P, Q, R, A, B, C = map(Sym, ('P', 'Q', 'R', 'A', 'B', 'C'))
    s = Imp(And(P, Q), R)
    assert symbols(s) == {'P', 'Q', 'R'} and to_str(s) == '((P & Q) => R)'
    assert symbols(Iff(P, Not(Q))) == {'P', 'Q'}
    assert to_str(Or(Not(P), And(Q, R))) == '(~P | (Q & R))'
    m = {'P': True, 'Q': False, 'R': True}
    assert pl_true(s, m) is True
    assert pl_true(Iff(P, Q), m) is False
    assert pl_true(Or(Not(P), Q), m) is False
    mp = tt_entails(And(P, Imp(P, Q)), Q)
    mt = tt_entails(And(Not(Q), Imp(P, Q)), Not(P))
    assert mp == (True, 4) and mt == (True, 4)
    assert tt_entails(Or(P, Q), P)[0] is False
    assert is_valid(Or(P, Not(P)))
    assert not is_satisfiable(And(P, Not(P)))
    de_morgan = [
        {'P': model['P'], 'Q': model['Q'],
         'not_and': pl_true(Not(And(P, Q)), model),
         'or_not': pl_true(Or(Not(P), Not(Q)), model)}
        for model in all_models({'P', 'Q'})]
    assert all(r['not_and'] == r['or_not'] for r in de_morgan)
    assert to_clauses(Iff(B, Or(A, C))) == {
        frozenset(('~B', 'A', 'C')), frozenset(('~A', 'B')), frozenset(('~C', 'B'))}
    examples = [Iff(B, Or(A, C)), Imp(And(P, Q), R),
                Not(Or(P, And(Q, R))), Iff(Imp(P, Q), Or(Q, R))]
    for formula in examples:
        cnf = to_cnf(formula)
        assert all(pl_true(formula, m) == pl_true(cnf, m)
                   for m in all_models(symbols(formula)))
    assert to_clauses(Or(P, Not(P))) == set()
    assert resolve(frozenset(('A', 'B')), frozenset(('~A', 'C'))) == [frozenset(('B', 'C'))]
    assert resolve(frozenset(('C',)), frozenset(('~C',))) == [frozenset()]
    assert resolve(frozenset(('A', 'B')), frozenset(('~A', '~B'))) == []
    kb = conjoin([Or(A, B), Or(Not(A), C), Or(Not(B), C)])
    for query, expected in ((C, True), (A, False)):
        assert tt_entails(kb, query)[0] == pl_resolution(to_clauses(kb), query) == expected
    sat_clauses = [frozenset(c) for c in [('A',), ('~A', 'B'), ('~B', 'C'),
                                       ('~C', 'D', 'E'), ('~D', '~E')]]
    stats = {}
    sat_model = dpll_satisfiable(sat_clauses, stats)
    assert sat_model is not False
    assert all(sat_model[x] for x in ('A', 'B', 'C'))
    assert sat_model['D'] != sat_model['E']
    unsat_clauses = [frozenset(c) for c in [('A', 'B'), ('~A', 'B'),
                                         ('A', '~B'), ('~A', '~B')]]
    assert dpll_satisfiable(unsat_clauses) is False
    assert dpll_satisfiable(to_clauses(kb) | to_clauses(Not(C))) is False
    assert dpll_satisfiable(set()) == {}
    assert dpll_satisfiable({frozenset()}) is False
    assert resolution_unsat(set()) == (False, 0)
    assert resolution_unsat({frozenset()}) == (True, 0)
    assert tt_entails(Or(P, Not(P)), Or(P, Not(P)), limit=1) == (None, 2)
    assert resolution_unsat({frozenset(('P',)), frozenset(('~P',))}, limit=0) == (None, 1)
    assert find_pure_symbol({'A'}, [frozenset(('~A', 'B'))], {}) == ('A', False)
    assert find_unit_clause([frozenset(('~A', 'B'))], {'A': True}) == ('B', True)
    wumpus = solve_wumpus()
    return {'status': 'PASS', 'steps': 8, 'modus_ponens': mp, 'modus_tollens': mt,
            'de_morgan': de_morgan, 'cnf_equivalence_examples': len(examples),
            'dpll_example_model': sat_model, 'wumpus': wumpus}


def verify_small_crosschecks():
    """SAT аргуудыг бүх 2 хувьсагчтай CNF болон 4 хувьсагчтай жишээнд тулгана."""
    possible = [frozenset(lit for lit in (a, b) if lit is not None)
                for a in (None, 'A', '~A') for b in (None, 'B', '~B')]
    checked = 0
    for mask in range(1 << len(possible)):
        clauses = {c for i, c in enumerate(possible) if mask & (1 << i)}
        sat = tt_satisfiable_clauses(clauses)[0]
        unsat = resolution_unsat(clauses)[0]
        model = dpll_satisfiable(clauses)
        assert sat == (not unsat) == (model is not False)
        if model is not False:
            assert all(clause_value(c, model) is True for c in clauses)
        checked += 1
    for seed in range(20):
        clauses = random_3sat(4, 16, seed)
        sat = tt_satisfiable_clauses(clauses)[0]
        assert sat == (not resolution_unsat(clauses)[0]) == (dpll_satisfiable(clauses) is not False)
        checked += 1
    rng = random.Random(9)
    atoms = [Sym('P'), Sym('Q'), Sym('R')]
    def sentence(depth):
        if depth == 0:
            return rng.choice(atoms)
        op = rng.choice((Not, And, Or, Imp, Iff))
        return op(sentence(depth-1)) if op is Not else op(sentence(depth-1), sentence(depth-1))
    for _ in range(60):
        formula = sentence(3)
        cnf = to_cnf(formula)
        for model in all_models(symbols(formula)):
            truth = pl_true(formula, model)
            assert truth == pl_true(cnf, model)
            assert truth == all(clause_value(c, model) is True for c in to_clauses(formula))
    return {'status': 'PASS', 'sat_crosschecks': checked, 'cnf_random_formulas': 60}


def main():
    required = verify_required_steps()
    crosschecks = verify_small_crosschecks()
    benchmarks = run_benchmarks(required['wumpus'])
    result = {'environment': {'python': sys.version.split()[0], 'platform': platform.platform()},
              'seed': 1, 'limits': {'models': MODEL_LIMIT, 'resolvents': RESOLVENT_LIMIT},
              'required_checks': required, 'crosschecks': crosschecks, 'benchmarks': benchmarks}
    destination = Path(__file__).with_name('Lab5_Results.json')
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print('Үндсэн 1-8-р алхмын шалгалт: PASS')
    print(f"SAT тулгалт: {crosschecks['sat_crosschecks']}; CNF нэмэлт жишээ: 60")
    print('Wumpus KB-ийг хангах загвар:', required['wumpus']['model_count'])
    for row in benchmarks:
        print(row['problem'], '| result =', row['result'],
              '| TT =', row['tt_result'], row['tt_models'],
              '| Resolution =', row['res_result'], row['resolvents'],
              '| DPLL =', row['dpll_result'], row['dpll_calls'])
    print('Үр дүн:', destination.name)
    return result


if __name__ == '__main__':
    main()
