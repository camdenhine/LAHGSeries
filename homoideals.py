import numpy as np
import warnings
import itertools
import functools
from sage.all import ZZ
from sage.all import CC
from sage.all import matrix
from sage.all import vector
from sage.all import macaulay2
from sage.all import DiGraph
from sage.combinat.posets.posets import FinitePoset
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.ideal import Ideal

from sage.interfaces.four_ti_2 import four_ti_2
from sage.numerical.mip import MIPSolverException
from sage.numerical.mip import *
from fakeexps import *
from itertools import combinations

def nsupp(A, v):
	
	m = A.ncols()
	n = A.nrows()
	l = [i for i in range(m)]
	indices_list = []
	sample_set = set(l)
	for n in range(len(sample_set) + 1):
		indices_list += list(combinations(sample_set, n))
	del l
	del sample_set
	supports = []
	for indices in indices_list:
		p = MixedIntegerLinearProgram()
		p.set_objective(None)
		u = p.new_variable(integer=True)
		p.add_constraint(A*u == 0)

		for k in range(n):
			if k in indices:
				if v[k].is_integer():
					p.add_constraint(u[k] + v[k] <= -1)
				else:
					p.add_constraint(u[k] + v[k] <= 0)
			else:
				p.add_constraint(u[k] + v[k] >= 0)
		try:
			p.solve()
			supports.append(set(indices))
		except MIPSolverException:
			pass
	return supports
	
def grobner_base(A, w):

	file_name = four_ti_2.temp_project()
	pr = four_ti_2._process_input(
		{'project': file_name,
		'mat': A,
		'cost': w})
		
	four_ti_2.call("groebner", file_name, verbose=False, options=["--algorithm=weighted", "-parb"])
	G = four_ti_2.read_matrix(file_name + ".gro")
	return G

def check_1(A, w, v, supports):

	GT = grobner_base(A, w).transpose()
	N = []
	Nc = []
	n = GT.nrows()
	m = GT.ncols()
	for indices in supports:
		p = MixedIntegerLinearProgram()
		p.set_objective(None)
		u = p.new_variable(integer=True)
		c = p.new_variable(integer=True)
		
		j = 0
		for r in GT.rows():
    			p.add_constraint(sum([c[l]*r[l] for l in range(m)]) == u[j])
    			j+=1
    			
		for i in range(m):
			p.add_constraint(c[i] >= 0)
		
		for k in range(n):
			if k in indices:
				if v[k].is_integer():
					p.add_constraint(u[k] + v[k] <= -1)
				else:
					p.add_constraint(u[k] + v[k] <= 0)
			else:
				p.add_constraint(u[k] + v[k] >= 0)
		try:
			p.solve()
			N.append(indices)
		except MIPSolverException:
			Nc.append(indices)
	return N
	
def orthog_check(A, w, v, I):
	
	N = []
	Nc = []
	G = grobner_base(A, w)
	p = MixedIntegerLinearProgram()
	p.set_objective(None)
	u = p.new_variable(integer=True)
	c = p.new_variable(integer=True)
	V = VectorSpace(GF(G.nrows()),G.ncols())
	U = V.subspace(G)
	G_perp = U.complement().basis_matrix()
	M = G_perp.transpose()
	n = M.nrows()
	m = M.ncols()
	
	new_M = []
	for i in range(M.nrows()):
		r = M[i]
		new_r = []
		for j in range(M.ncols()):
			new_r.append(int(M[i].list()[j]))
		new_M.append(new_r)
	M = matrix(ZZ, new_M)
	
	j = 0
	for r in M.rows():
    		p.add_constraint(sum([c[l]*r[l] for l in range(m)]) == u[j])
    		j+=1
    		
	p.add_constraint(A*u == 0)
		
	for k in range(G.ncols()):
		if k in I:
			if v[k].is_integer():
				p.add_constraint(u[k] + v[k] <= -1)
			else:
				p.add_constraint(u[k] + v[k] <= 0)
		else:
			p.add_constraint(u[k] + v[k] >= 0)
	try:
		p.solve()
		return False
	except MIPSolverException:
		return True
		
def bruteforce_check1(A, w, v, I, bound):
	u = []
	Acols = A.ncols()
	Arows = A.nrows()
	G = grobner_base(A, w)
	GT = G.transpose()
	n = GT.nrows()
	m = GT.ncols()
	for k in range(Acols):
		u.append(-1*bound)
	stop = False
	def check_previous(u, i):
		while u[i] <= bound:
			if u[Acols-1] > bound:
				return
			if i > 0:
				check, return_u = check_previous(u, i - 1)
				if check == False:
					return False, return_u
			else:
				#print(u)
				tryU = True
				for k in range(Acols):
					if k in I:
						if u[k] + v[k] >= 0:
							tryU = False
					else:
						if u[k] + v[k] < 0:
							tryU = False
				u_1 = vector(ZZ, u)
				if A*u_1 != vector(ZZ, [0]*Arows):
					tryU = False
				if tryU == True:
					p = MixedIntegerLinearProgram()
					p.set_objective(None)
					c = p.new_variable(integer=True)
					j = 0
					for r in GT.rows():
						p.add_constraint(sum([c[l]*r[l] for l in range(m)]) == u_1[j])
						j+=1
							
					for i in range(m):
						p.add_constraint(c[i] >= 0)
						
					try:
						p.solve()
					except MIPSolverException:
						return False, u
						#print(A*u_1)
					
			u[i]+=1
		if i == Acols - 1:
			return True, []
		u[i] = -1*bound
		return True, []
	j = Acols - 1
	
	return check_previous(u, j)
	
def bruteforce_check2(A, w, v, I, bound):
	Acols = A.ncols()
	Arows = A.nrows()
	G = grobner_base(A, w)
	GT = G.transpose()
	n = GT.nrows()
	m = GT.ncols()
	prod = [q for q in itertools.product([0, 1, 2], repeat=n)]
	prod.pop()
	k = 1
	while k <= bound:
		for J in prod:
			p = MixedIntegerLinearProgram()
			p.set_objective(None)
			u = p.new_variable(integer=True)
			c = p.new_variable(integer=True)
			
			for k in range(Acols):
				if k in I:
					if v[k].is_integer():
						p.add_constraint(u[k] + v[k] <= -1)
					else:
						p.add_constraint(u[k] + v[k] <= 0)
				else:
					p.add_constraint(u[k] + v[k] >= 0)
					
			p.add_constraint(A*u == 0)
			
			for j in range(len(J)):
				if J[j] == 0:
					p.add_constraint(sum([c[l]*GT.rows()[j][l] for l in range(m)]) >= u[j] + k)
				elif J[j] == 1:
					p.add_constraint(sum([c[l]*GT.rows()[j][l] for l in range(m)]) <= u[j] - k)
				else:
					p.add_constraint(sum([c[l]*GT.rows()[j][l] for l in range(m)]) == u[j])
			
			for i in range(m):
				p.add_constraint(c[i] >= 0)
			
			try:
				p.solve()
				u_0 = p.get_values(u)
				p_0 = MixedIntegerLinearProgram()
				p_0.set_objective(None)
				c_0 = p_0.new_variable(integer=True)
				j = 0
				
				for r in GT.rows():
					p_0.add_constraint(sum([c_0[l]*r[l] for l in range(m)]) == u_0[j])
					j+=1
				for i in range(m):
					p_0.add_constraint(c_0[i] >= 0)
				try:
					p_0.solve()
					
				except MIPSolverException:
					return False, vector(ZZ, list(u_0.values()))
			except MIPSolverException:
				prod.remove(J)
		k+=1
	return True, []

def check_all_brute2(A, w, v, NS, bound):
	for I in NS:
		for i in range(bound):
			b, u = bruteforce_check2(A, w, v, I, bound)
			if b == False:
				NS.remove(I)
				break
	return NS
	
def check_2(A, w, v, N, Nc):
	True == True
	
def get_NSc(A, v, N):
	supports = nsupp(A, v)
	Nc = [I for I in supports if I not in N]
	return Nc
	
def NS_to_N(A, v, B, NS):
	NSc = get_NSc(A, v, NS)
	N = []
	Nc = []
	supp = set([])
	n = 0
	for r in B.rows():
		for k in r:
			if k != 0:
				supp.add(n)
		
		n+=1
	I0 = set([])
	for k in range(len(v)):
		if v[k] < 0:
			I0.add(k)
	rhs = I0.union(supp)
	total = set([i for i in range(len(v))])
	complement = total - rhs
	for Iu in NS:
		if Iu.union(supp) == rhs:
			N.append(Iu)
	for Iu in NSc:
		if Iu.union(supp) == rhs:
			Nc.append(Iu)
	return N, Nc
	
def get_K_N(N):
	K = N[0]
	for I in N:
		K = K.intersection(I)
	return K
	
def get_ind(N, Nc):

	K = get_K_N(N)	
	exps = set([])
	for I in N:
		for J in Nc:
			exps.add(frozenset(I.union(J) - K))
		
	return exps
		
def get_gens(B, ind):

	n = B.ncols()
	R = PolynomialRing(CC, n,'s')
	R.inject_variables()
	vec = B * vector(R, R.gens())
	gen = []
	for i in ind:
		a = 1
		for k in i:
			a = a * vec[k]
		gen.append(a)
		
	I = Ideal(R, gen)
	gb = I.groebner_basis()
	gb = gb.reduced()
	return gb
	
def get_P(A, v, B, NS):

	N, Nc = NS_to_N(A, v, B, NS)
	ind = get_ind(N, Nc)
	gens = get_gens(B, ind)
	n = B.ncols()
	R = PolynomialRing(CC, n,'s')
	R.inject_variables()
	return Ideal(R, gens)
		
		
		
		
		
		
