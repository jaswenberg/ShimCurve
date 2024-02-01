/*
 Weil polynomials downloaded from the LMFDB on 18 November 2022.
 Below is a list (called data), collecting the weight 1 L-polynomial
 attached to each isogeny class of an abelian variety.

*/
P<x> := PolynomialRing(Integers()); 
data := [*\
49*x^4 - 70*x^3 + 39*x^2 - 10*x + 1,\
49*x^4 - 63*x^3 + 34*x^2 - 9*x + 1,\
49*x^4 - 56*x^3 + 29*x^2 - 8*x + 1,\
49*x^4 - 56*x^3 + 30*x^2 - 8*x + 1,\
49*x^4 - 49*x^3 + 24*x^2 - 7*x + 1,\
49*x^4 - 49*x^3 + 26*x^2 - 7*x + 1,\
49*x^4 - 42*x^3 + 18*x^2 - 6*x + 1,\
49*x^4 - 42*x^3 + 19*x^2 - 6*x + 1,\
49*x^4 - 42*x^3 + 22*x^2 - 6*x + 1,\
49*x^4 - 42*x^3 + 23*x^2 - 6*x + 1,\
49*x^4 - 35*x^3 + 14*x^2 - 5*x + 1,\
49*x^4 - 35*x^3 + 18*x^2 - 5*x + 1,\
49*x^4 - 35*x^3 + 20*x^2 - 5*x + 1,\
49*x^4 - 28*x^3 + 8*x^2 - 4*x + 1,\
49*x^4 - 28*x^3 + 9*x^2 - 4*x + 1,\
49*x^4 - 28*x^3 + 14*x^2 - 4*x + 1,\
49*x^4 - 28*x^3 + 17*x^2 - 4*x + 1,\
49*x^4 - 28*x^3 + 18*x^2 - 4*x + 1,\
49*x^4 - 21*x^3 + 2*x^2 - 3*x + 1,\
49*x^4 - 21*x^3 + 4*x^2 - 3*x + 1,\
49*x^4 - 21*x^3 + 10*x^2 - 3*x + 1,\
49*x^4 - 21*x^3 + 14*x^2 - 3*x + 1,\
49*x^4 - 21*x^3 + 16*x^2 - 3*x + 1,\
49*x^4 - 14*x^3 - 3*x^2 - 2*x + 1,\
49*x^4 - 14*x^3 - x^2 - 2*x + 1,\
49*x^4 - 14*x^3 + 2*x^2 - 2*x + 1,\
49*x^4 - 14*x^3 + 6*x^2 - 2*x + 1,\
49*x^4 - 14*x^3 + 11*x^2 - 2*x + 1,\
49*x^4 - 14*x^3 + 14*x^2 - 2*x + 1,\
49*x^4 - 14*x^3 + 15*x^2 - 2*x + 1,\
49*x^4 - 7*x^3 - 6*x^2 - x + 1,\
49*x^4 - 7*x^3 + 2*x^2 - x + 1,\
49*x^4 - 7*x^3 + 8*x^2 - x + 1,\
49*x^4 - 7*x^3 + 12*x^2 - x + 1,\
49*x^4 - 7*x^3 + 14*x^2 - x + 1,\
49*x^4 - 14*x^2 + 1,\
49*x^4 - 13*x^2 + 1,\
49*x^4 - 12*x^2 + 1,\
49*x^4 - 11*x^2 + 1,\
49*x^4 - 10*x^2 + 1,\
49*x^4 - 9*x^2 + 1,\
49*x^4 - 8*x^2 + 1,\
49*x^4 - 7*x^2 + 1,\
49*x^4 - 6*x^2 + 1,\
49*x^4 - 5*x^2 + 1,\
49*x^4 - 4*x^2 + 1,\
49*x^4 - 3*x^2 + 1,\
49*x^4 - 2*x^2 + 1,\
49*x^4 - x^2 + 1,\
49*x^4 + 1,\
49*x^4 + x^2 + 1,\
49*x^4 + 2*x^2 + 1,\
49*x^4 + 3*x^2 + 1,\
49*x^4 + 4*x^2 + 1,\
49*x^4 + 5*x^2 + 1,\
49*x^4 + 6*x^2 + 1,\
49*x^4 + 7*x^2 + 1,\
49*x^4 + 8*x^2 + 1,\
49*x^4 + 9*x^2 + 1,\
49*x^4 + 10*x^2 + 1,\
49*x^4 + 11*x^2 + 1,\
49*x^4 + 12*x^2 + 1,\
49*x^4 + 13*x^2 + 1,\
49*x^4 + 14*x^2 + 1,\
49*x^4 + 7*x^3 - 6*x^2 + x + 1,\
49*x^4 + 7*x^3 + 2*x^2 + x + 1,\
49*x^4 + 7*x^3 + 8*x^2 + x + 1,\
49*x^4 + 7*x^3 + 12*x^2 + x + 1,\
49*x^4 + 7*x^3 + 14*x^2 + x + 1,\
49*x^4 + 14*x^3 - 3*x^2 + 2*x + 1,\
49*x^4 + 14*x^3 - x^2 + 2*x + 1,\
49*x^4 + 14*x^3 + 2*x^2 + 2*x + 1,\
49*x^4 + 14*x^3 + 6*x^2 + 2*x + 1,\
49*x^4 + 14*x^3 + 11*x^2 + 2*x + 1,\
49*x^4 + 14*x^3 + 14*x^2 + 2*x + 1,\
49*x^4 + 14*x^3 + 15*x^2 + 2*x + 1,\
49*x^4 + 21*x^3 + 2*x^2 + 3*x + 1,\
49*x^4 + 21*x^3 + 4*x^2 + 3*x + 1,\
49*x^4 + 21*x^3 + 10*x^2 + 3*x + 1,\
49*x^4 + 21*x^3 + 14*x^2 + 3*x + 1,\
49*x^4 + 21*x^3 + 16*x^2 + 3*x + 1,\
49*x^4 + 28*x^3 + 8*x^2 + 4*x + 1,\
49*x^4 + 28*x^3 + 9*x^2 + 4*x + 1,\
49*x^4 + 28*x^3 + 14*x^2 + 4*x + 1,\
49*x^4 + 28*x^3 + 17*x^2 + 4*x + 1,\
49*x^4 + 28*x^3 + 18*x^2 + 4*x + 1,\
49*x^4 + 35*x^3 + 14*x^2 + 5*x + 1,\
49*x^4 + 35*x^3 + 18*x^2 + 5*x + 1,\
49*x^4 + 35*x^3 + 20*x^2 + 5*x + 1,\
49*x^4 + 42*x^3 + 18*x^2 + 6*x + 1,\
49*x^4 + 42*x^3 + 19*x^2 + 6*x + 1,\
49*x^4 + 42*x^3 + 22*x^2 + 6*x + 1,\
49*x^4 + 42*x^3 + 23*x^2 + 6*x + 1,\
49*x^4 + 49*x^3 + 24*x^2 + 7*x + 1,\
49*x^4 + 49*x^3 + 26*x^2 + 7*x + 1,\
49*x^4 + 56*x^3 + 29*x^2 + 8*x + 1,\
49*x^4 + 56*x^3 + 30*x^2 + 8*x + 1,\
49*x^4 + 63*x^3 + 34*x^2 + 9*x + 1,\
49*x^4 + 70*x^3 + 39*x^2 + 10*x + 1*]
;