# Lfuncff
Source code behind the paper [arXiv link] and my thesis [link]. It computes the L-functions of twisted elliptic curves over rational function fields (F_p[t]) and goes through all conductors of a given degree. PrincipalLegendre computes the twists of y^2=x(x-1)(x-t), PrincipalDavid computes the twists of y^2=(x-1)(x-2t^2-1)(x-t^2), and PrincipalDirichlet computes the twists of P^1.

# Instructions
-Works best with Eclipse: https://www.eclipse.org/

-Settings can be changed after "public static void main(String args[])"

-The code is unoptimized, messy, and lack comments. Please contact antoine[dot]comeau-lapointe[at]concordia[dot]ca for support.

# Console output interpretation example (using p=29;d=2;ell=7)
**n=1**                              ----- degree of field extension of F_p to compute the characters

**1**                                ----- primes of degree 1 constructed

**Primes: OK**                       ----- all necessary primes were constructed

**F_q: OK**                          ----- F_q (=F_p^n) was succesfully constructed

**Factoring: OK**                    ----- factorization of primes over F_p^n successfully constructed

**alpha: 25,24,28,4,20,12,0,1**      ----- representative for alpha, it reads as (25+24e^(2\*i\*pi/7)+28e^(4\*i\*pi/7)+4e^(6\*i\*pi/7)+20e^(8\*i\*pi/7)+12e^(10\*i\*pi/7)+0e^(12\*i\*pi/7)/29^1

**rank 0: 2512**                     ----- number of curves with rank 0

**i root: 0**                        ----- number of curves with i as root

**i root symmetry:true**             ----- testing if having i as a root implies -i as root

**cursed:0**                         ----- number of curves that needs the conjecture to be evaluated

**conjecture:true**                  ----- if conjecture on sign of functional equation is true, Legendre only

**time:1805ms**                      ----- running time

# Todo
-Arbitrary elliptic curves

-Composite orders

-Implement Schoof's algorithm

-Elliptic curves over extensions of F_q[t]
