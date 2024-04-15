import numpy as np
import warnings
import itertools
import functools
from sage.all import ZZ
from sage.all import matrix
from sage.all import macaulay2
from sage.all import DiGraph
from sage.combinat.posets.posets import FinitePoset

from stdpairs import *
from sage.interfaces.four_ti_2 import four_ti_2
from sage.numerical.mip import MIPSolverException


def in_I_Aw(A, w):

	file_name = four_ti_2.temp_project()
	pr = four_ti_2._process_input(
		{'project': file_name,
		'mat': A,
		'cost': w})
		
	four_ti_2.call("groebner", file_name, verbose=False, options=["--algorithm=weighted", "-parb"])
	G = four_ti_2.read_matrix(file_name + ".gro")
	
	initial = []
	for v in G:
		temp = []
		for l in v:
			if l < 0:
				temp.append(0)
			else:
				temp.append(int(l))
				
		initial.append(temp)
	initial = matrix(ZZ, initial)
	return initial
		
	
def standard_pairs(A, w):

	n = len(A[0])
	P = matrix.identity(n)
	Q = AffineMonoid(P)
	M = in_I_Aw(A, w).transpose()
	I = MonomialIdeal(M,Q)
	S = I.standard_cover()
	return S
	

def fexps(A, b, w):
	
	S = standard_pairs(A, w)
	exps = {}
	for s in S:
		exps[s] = []
		indices = [i for i in s]
		#print(indices)
		for i in range(len(S[s])):
			monomial = S[s][i].monomial().flatten().tolist()
			p = MixedIntegerLinearProgram()
			p.set_objective(None)
			v = p.new_variable(real=True)
			p.add_constraint(A * v == b)
			for k in range(len(monomial)):
				if monomial[k] == 1:
					p.add_constraint(v[k] == 1)
				elif k not in indices:
					p.add_constraint(v[k] == 0)
			try:
				p.solve()
				exps[s].append(list(p.get_values(v).values()))
				
			except MIPSolverException:
				exps[s].append([])
		
	return exps
	
def eigenprojection(A, B): #this is no longer being used

	PA = A*((A.transpose()*A).inverse())*(A.transpose())
	PB = B*((B.transpose()*B).inverse())*(B.transpose())
	M = PA*PB
	
	eigenv = M.eigenvectors_right()
	v = []
	for k in range(len(eigenv)):
		if eigenv[k][0] == 1 and eigenv[k][2] == 1:
			v = eigenv[k][1]
	return v
	
	
def soltocols(S):
    temp = []
    temp.append(list(i for i in S[0][0]))
    for r in S[2]:
        temp.append(list(i for i in r))
    M = matrix(ZZ, temp).transpose()
    return M
