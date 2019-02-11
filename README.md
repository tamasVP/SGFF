# SGFF
Multi-soliton form factors in sine-Gordon model

Nature of problem:
The multi-soliton form factors, i.e. matrix elements of local operators, of the sine-Gordon model (relevant in two dimensional physics) were given only by highly nontrivial integral representation with a limited domain of convergence. Practical applications of the form factors, e.g. calculation of correlation functions in two dimensional condensed matter systems, were not possible in general.

Solution method:
Using analytic continuation techniques an efficient algorithm is found and implemented in Mathematica, which provides a general and systematic way to calculate multi-soliton form factors in the sine-Gordon model. The package contains routines to compute the two-, four- and six-soliton form factors.

Main functions include FF2, FF4, FF6 calculating generic 2-, 4- and 6 particle form factors of the exponential operator. FF2p, FF4p and FF6p calculate form factors for physical rapidities. Parameters describing the specific operator and various regulators may be specified in the main package, "SGFF.m."

Simple examples are included in the notebook "sgfftest.nb."

Further description can be found in 
T. Palmai. Regularization of multi-soliton form factors in sine-Gordon model, Comput. Phys. Commun. 183(2012)1813.
