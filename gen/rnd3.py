# Generate random 3-sat problems

import math
import numpy as np
import random
import argparse

def write_dimacs_to(n_vars, iclauses, out_filename):
    with open(out_filename, 'w') as f:
        f.write("p cnf %d %d\n" % (n_vars, len(iclauses)))
        for c in iclauses:
            for x in c:
                f.write("%d " % x)
            f.write("0\n")

def mk_out_filename(opts, n_vars, t):
    prefix = "%s/sr_n=%.4d_ncm=%.2f_ncs=%.2f_t=%.4d" % \
            (opts.out_dir, opts.nc_m, opts.nc_s, n_vars, t)
    return "%s.dimacs" % prefix

def generate_k_iclause(n, k):
    vs = np.random.choice(n, size=min(n, k), replace=False)
    return [v + 1 if random.random() < 0.5 else -(v + 1) for v in vs]

def gen_clause(opts):
    n = random.randint(opts.min_n, opts.max_n)

    clauses = []
    for _ in range(int(n * np.random.normal(opts.nc_m, opts.nc_s))):
        clause = generate_k_iclause(n, 3)
        clauses.append(clause)

    return n, clauses

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('out_dir', action='store', type=str)
    parser.add_argument('n_pblms', action='store', type=int)

    # number of variables
    parser.add_argument('--min_n', action='store', dest='min_n', type=int, default=10)
    parser.add_argument('--max_n', action='store', dest='max_n', type=int, default=10)

    # mean and standard deviation for #clauses / #literals
    parser.add_argument('--nc_mean', action='store', dest='nc_m', type=float, default=4.2)
    parser.add_argument('--nc_stdv', action='store', dest='nc_s', type=float, default=0.2)

    parser.add_argument('--py_seed', action='store', dest='py_seed', type=int, default=None)
    parser.add_argument('--np_seed', action='store', dest='np_seed', type=int, default=None)

    opts = parser.parse_args()

    if opts.py_seed is not None: random.seed(opts.py_seed)
    if opts.np_seed is not None: np.random.seed(opts.np_seed)

    for pb in range(opts.n_pblms):
        n_vars, clauses = gen_clause(opts)
        out_filename = mk_out_filename(opts, n_vars, pb)
        write_dimacs_to(n_vars, clauses, out_filename)
