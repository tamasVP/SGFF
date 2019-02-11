(* ::Package:: *)

(*(********************************************************************)*)
(*(*********************SGFF Mathematica Package***********************)*)
(*(***for calculating multisoliton form factors in sine-Gordon model***)*)
(*(********************************************************************)*)
(* *)
(*(*Output:*)
(*FF2={Subscript[F, +-],Subscript[F, -+]}*)
(*FF4={Subscript[F, --++],Subscript[F, -+-+],Subscript[F, +--+],Subscript[F, -++-],Subscript[F, +-+-],Subscript[F, ++--]}*)
(*FF6={Subscript[F, +++---],Subscript[F, ++-+--],Subscript[F, ++--+-],Subscript[F, ++---+],Subscript[F, +-+-+-],Subscript[F, +-++--],Subscript[F, +-+--+],Subscript[F, +--++-],Subscript[F, +--+-+],Subscript[F, +---++],Subscript[F, -+++--],Subscript[F, -++-+-],Subscript[F, -++--+],Subscript[F, -+-++-],Subscript[F, -+--++],Subscript[F, -+-+-+],Subscript[F, --+++-],Subscript[F, --++-+],Subscript[F, --+-++],Subscript[F, ---+++]}*)*)


(*******************************************************************)
(****************************PARAMETERS*****************************)
(*******************************************************************)

\[Xi]=1+1/1000; (*xi sine-Gordon parameter*)
aover\[Beta]=1; (*exponent of the operator*)
NN=3; (*regularization parameter for G- and W-functions*)
Na=10; (*max orders in asymptotic series to treat*)
Ni=500; (*interpolation points for W-functions*)
\[Epsilon]=10^-9; (*displacement for residue calculations*)
aa=0; (*lower bound for intergrals*)
bb=15; (*upper bound for intergrals*)


(*******************************************************************)
(***************************PRELIMINARIES***************************)
(*******************************************************************)

A=-2*aover\[Beta]-1/\[Xi];

(*Subscript[C, 1] and Subscript[C, 2] constants*)
C1=N[Exp[-NIntegrate[Sinh[t/2]^2*Sinh[t*(\[Xi]-1)]/Sinh[2*t]/Sinh[\[Xi]*t]/Cosh[t]/t,{t,0,20},WorkingPrecision->50]],50];
C2=N[Exp[4*NIntegrate[Sinh[t/2]^2*Sinh[t*(\[Xi]-1)]/Sinh[2*t]/Sinh[\[Xi]*t]/t,{t,0,50},WorkingPrecision->50]],50];

(*G (\[CapitalTheta]) function*)
gG[Th_,k_]:=Gamma[((2*k+1+\[Xi])*Pi-I*Th)/(Pi*\[Xi])]*Gamma[(2*k+1)/\[Xi]]^2*Gamma[((2*k+1)*Pi-I*Th)/(Pi*\[Xi])]*Gamma[((2*k-1)*Pi+I*Th)/(Pi*\[Xi])]*Gamma[(2*k-1+\[Xi])/\[Xi]]^2*Gamma[((2*k-1+\[Xi])*Pi+I*Th)/(Pi*\[Xi])]/(Gamma[(2*k+\[Xi])/\[Xi]]^2*Gamma[((2*k+\[Xi])*Pi-I*Th)/(Pi*\[Xi])]*Gamma[((2*k-2+\[Xi])*Pi+I*Th)/(Pi*\[Xi])]*Gamma[(2*k)/\[Xi]]^2*Gamma[((2*k+2)*Pi-I*Th)/(Pi*\[Xi])]*Gamma[(2*k*Pi+I*Th)/(Pi*\[Xi])]);
G[Th_]:=C1*I*Sinh[Th/2]*Product[gG[Th,k]^k,{k,1,NN}]*Exp[NIntegrate[Exp[-4*NN*t]*(1+NN-NN*Exp[-4*t])*Sinh[t*(1-I*Th/Pi)]^2*Sinh[t*(\[Xi]-1)]/Sinh[2*t]/Sinh[\[Xi]*t]/Cosh[t]/t,{t,0,100}]];

(*W (\[CapitalTheta]) function*)
gW[Th_,k_]:=(Gamma[1+(2*k-5/2+I*Th/Pi)/\[Xi]]*Gamma[1+(2*k-1/2-I*Th/Pi)/\[Xi]]*Gamma[(2*k-1/2)/\[Xi]]^2)/(Gamma[1+(2*k-3/2)/\[Xi]]^2*Gamma[(2*k+1/2-I*Th/Pi)/\[Xi]]*Gamma[(2*k-3/2+I*Th/Pi)/\[Xi]]);
W[Th_]:=-2/Cosh[Th]*Product[gW[Th,k],{k,1,NN}]*Exp[-2*NIntegrate[Exp[-4*NN*t]*Sinh[t*(1-I*Th/Pi)]^2*Sinh[t*(\[Xi]-1)]/Sinh[2*t]/Sinh[t*\[Xi]]/t,{t,0,100}]];

(*Subscript[\[Alpha], k] exponents for the 4-soliton formula*)
alphaG4={-1-1/\[Xi],1-1/\[Xi],1/\[Xi]-1,1+1/\[Xi]};
(*Subscript[\[Alpha], k] exponents for the 6-soliton formula*)
alphaG6=2*{0,1,-1,1/\[Xi],-1/\[Xi],-1-1/\[Xi],1-1/\[Xi],1/\[Xi]-1,1+1/\[Xi]};

(*Procedure PRO (\[GothicCapitalA],\[GothicCapitalB]) creates products of asymototic series*)
PRO[\[GothicCapitalA]_,\[GothicCapitalB]_]:=Module[{MM,Szo,j,n,l},MM=Min[Max[\[GothicCapitalA][[All,2]]],Max[\[GothicCapitalB][[All,2]]]];Szo=Table[{\[GothicCapitalA][[Ceiling[j/Dimensions[\[GothicCapitalB]][[1]]],1]]*\[GothicCapitalB][[j-(Ceiling[j/Dimensions[\[GothicCapitalB]][[1]]]-1)*Dimensions[\[GothicCapitalB]][[1]],1]],\[GothicCapitalA][[Ceiling[j/Dimensions[\[GothicCapitalB]][[1]]],2]]+\[GothicCapitalB][[j-(Ceiling[j/Dimensions[\[GothicCapitalB]][[1]]]-1)*Dimensions[\[GothicCapitalB]][[1]],2]]},{j,1,Dimensions[\[GothicCapitalA]][[1]]*Dimensions[\[GothicCapitalB]][[1]]}];For[j=1,j<1+Dimensions[Szo][[1]],j++,If[Szo[[j,2]]>MM,Szo=Drop[Szo,{j}];j--,0]];n=1;While[n<Dimensions[Szo][[1]],For[l=n+1,l<Dimensions[Szo][[1]]+1,l++,If[Szo[[n,2]]==Szo[[l,2]],Szo[[n,1]]=Szo[[n,1]]+Szo[[l,1]];Szo=Drop[Szo,{l}];l--]];n++];Szo];

(*Procedure NPRO (K,\[GothicCapitalA]) creates the product of an asymototic series and a single exponential function corresponding to K*)
NPRO[K_,\[GothicCapitalA]_]:=Module[{n,\[GothicCapitalB]},\[GothicCapitalB]=\[GothicCapitalA];For[n=1,n<Dimensions[\[GothicCapitalA]][[1]]+1,n++,\[GothicCapitalB][[n,1]]=\[GothicCapitalA][[n,1]]*K[[1]];\[GothicCapitalB][[n,2]]=\[GothicCapitalA][[n,2]]+K[[2]]];\[GothicCapitalB]];

(*Procedure Asyfun (\[GothicCapitalA],x) gives the value of the asymptotic series corresponding to \[GothicCapitalA] at x*)
Asyfun[\[GothicCapitalA]_,x_]:=Module[{i,Eo},Eo=0;For[i=1,i<Dimensions[\[GothicCapitalA]][[1]]+1,i++,Eo=Eo+\[GothicCapitalA][[i,1]]*Exp[-\[GothicCapitalA][[i,2]]*x]];Eo];

(*Procedure AInt (\[GothicCapitalA]) gives the integral of the asymptotic series corresponding to \[GothicCapitalA] on the negative half line*)
(*2-soliton case*)
AInt2[\[GothicCapitalA]_]:=Module[{i,dime,Eo},dime=Dimensions[\[GothicCapitalA]][[1]];Eo=Sum[If[Abs[\[GothicCapitalA][[j,2]]]==0,0,\[GothicCapitalA][[j,1]]/\[GothicCapitalA][[j,2]]],{j,1,dime}];Eo];
(*4-soliton case*)
AInt4[\[GothicCapitalA]_]:=Module[{i,dime,Eo},Eo=Table[0,{i,1,4}];dime=Dimensions[\[GothicCapitalA]][[1]];For[i=1,i<5,i++,Eo[[i]]=Sum[If[Abs[\[GothicCapitalA][[j,2]][[i]]]==0,0,\[GothicCapitalA][[j,1]]/\[GothicCapitalA][[j,2]][[i]]],{j,1,dime}]];Eo];
(*6-soliton case*)
AInt6[\[GothicCapitalA]_]:=Module[{i,dime,Eo},Eo=Table[0,{i,1,9}];dime=Dimensions[\[GothicCapitalA]][[1]];For[i=1,i<10,i++,Eo[[i]]=Sum[If[Abs[\[GothicCapitalA][[j,2]][[i]]]==0,0,\[GothicCapitalA][[j,1]]/\[GothicCapitalA][[j,2]][[i]]],{j,1,dime}]];Eo];

(*Procedure SHI (\[GothicCapitalA],a) gives the shifted asymptotic series*)
SHI[\[GothicCapitalA]_,a_]:=Module[{n,\[GothicCapitalB]},\[GothicCapitalB]=\[GothicCapitalA];For[n=1,n<Dimensions[\[GothicCapitalA]][[1]]+1,n++,\[GothicCapitalB][[n,1]]=\[GothicCapitalA][[n,1]]*Exp[\[GothicCapitalA][[n,2]]*a]];\[GothicCapitalB]];

(*Procedure IPR4 (I1,I2) corresponds to the operator P (a,b) in the paper*)
IPR4[I1_,I2_]:=Exp[I*Pi/\[Xi]]I1[[1]]*I2[[4]]-Exp[I*Pi/\[Xi]]*I1[[2]]*I2[[3]]-Exp[-I*Pi/\[Xi]]*I1[[3]]*I2[[2]]+Exp[-I*Pi/\[Xi]]I1[[4]]*I2[[1]];
(*Procedure IPR6 (I1,I2,I3) is the 6-soliton variant of IPR4 (I1,I2)*)
IPR6[I1_,I2_,I3_]:=-I1[[9]]*I2[[3]]*I3[[5]]*Exp[I*Pi/\[Xi]*(-3)]+I1[[8]]*I2[[2]]*I3[[5]]*Exp[I*Pi/\[Xi]*(-3)]+I1[[2]]*I2[[8]]*I3[[5]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[3]]*I2[[9]]*I3[[5]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[9]]*I2[[1]]*I3[[6]]*Exp[I*Pi/\[Xi]*(-3)]-I1[[4]]*I2[[2]]*I3[[6]]*Exp[I*Pi/\[Xi]*(-3)]-I1[[2]]*I2[[4]]*I3[[6]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[1]]*I2[[9]]*I3[[6]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[8]]*I2[[1]]*I3[[7]]*Exp[I*Pi/\[Xi]*(-3)]+I1[[4]]*I2[[3]]*I3[[7]]*Exp[I*Pi/\[Xi]*(-3)]+I1[[3]]*I2[[4]]*I3[[7]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[1]]*I2[[8]]*I3[[7]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[2]]*I2[[3]]*I3[[1]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[3]]*I2[[2]]*I3[[1]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[7]]*I2[[8]]*I3[[1]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[6]]*I2[[9]]*I3[[1]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[2]]*I2[[1]]*I3[[3]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[1]]*I2[[2]]*I3[[3]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[7]]*I2[[4]]*I3[[3]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[5]]*I2[[9]]*I3[[3]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[3]]*I2[[1]]*I3[[2]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[1]]*I2[[3]]*I3[[2]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[6]]*I2[[4]]*I3[[2]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[5]]*I2[[8]]*I3[[2]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[9]]*I2[[6]]*I3[[1]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[8]]*I2[[7]]*I3[[1]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[2]]*I2[[3]]*I3[[1]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[3]]*I2[[2]]*I3[[1]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[9]]*I2[[5]]*I3[[3]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[4]]*I2[[7]]*I3[[3]]*Exp[I*Pi/\[Xi]*(-1)]+I1[[2]]*I2[[1]]*I3[[3]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[1]]*I2[[2]]*I3[[3]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[8]]*I2[[5]]*I3[[2]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[4]]*I2[[6]]*I3[[2]]*Exp[I*Pi/\[Xi]*(-1)]-I1[[3]]*I2[[1]]*I3[[2]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[1]]*I2[[3]]*I3[[2]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[2]]*I2[[6]]*I3[[4]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[3]]*I2[[7]]*I3[[4]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[7]]*I2[[3]]*I3[[4]]*Exp[I*Pi/\[Xi]*(+3)]-I1[[6]]*I2[[2]]*I3[[4]]*Exp[I*Pi/\[Xi]*(+3)]+I1[[2]]*I2[[5]]*I3[[8]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[1]]*I2[[7]]*I3[[8]]*Exp[I*Pi/\[Xi]*(+1)]-I1[[7]]*I2[[1]]*I3[[8]]*Exp[I*Pi/\[Xi]*(+3)]+I1[[5]]*I2[[2]]*I3[[8]]*Exp[I*Pi/\[Xi]*(+3)]-I1[[3]]*I2[[5]]*I3[[9]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[1]]*I2[[6]]*I3[[9]]*Exp[I*Pi/\[Xi]*(+1)]+I1[[6]]*I2[[1]]*I3[[9]]*Exp[I*Pi/\[Xi]*(+3)]-I1[[5]]*I2[[3]]*I3[[9]]*Exp[I*Pi/\[Xi]*(+3)];

CA:=Table[{(-1)^j,2*j},{j,0,Na}] (*Asymptotic series of 1/(cos (x))*)

(*Asymptotic series of the exponent of W (x)*)
a[l_,s_]:=1/l*(If[OddQ[2*l/\[Xi]],0,Cos[2*Pi*l/\[Xi]]/Cos[Pi*l/\[Xi]]/2]-Sin[Pi*l/\[Xi]]*Sign[s]*I) (*Subscript[a, k] coefficients, depending on the s sign*)
b[l_]:=- 1/l*If[OddQ[l],If[EvenQ[l*\[Xi]],0,Cot[Pi*l*\[Xi]/2]*I^(l+1)],I^l] (*Subscript[b, k] coefficients*)
Z1[l_]:=Join[{{1,0}},Table[{a[l,+1]^j/(j!),2*j*l/\[Xi]},{j,1,Na}]] (*Here s=+1 is chosen!*)
Z2[l_]:=Join[{{1,0}},Table[{b[l]^j/(j!),l*j},{j,1,Na}]]
P1:=Module[{P,j},P=PRO[Z1[1],Z1[2]];For[j=3,j<Na+1,j++,P=PRO[P,Z1[j]]];P]
P2:=Module[{P,j},P=PRO[Z2[1],Z2[2]];For[j=3,j<Na+1,j++,P=PRO[P,Z2[j]]];P]
Iau=N[NPRO[{-4*I/Sqrt[C2*\[Xi]]*Exp[-I*Pi/2/\[Xi]],(\[Xi]+1)/\[Xi]/2},PRO[PRO[P1,P2],CA]]];

p[n_]:=I*Pi*(n*\[Xi]-1/2) (*nth \[Xi]-dependent pole of W (x)*)
r[n_]:=\[Epsilon]*W[p[n]+\[Epsilon]] (*residue of W (x) at the nth \[Xi]-dependent pole*)


(*Generating interpolation functions for the integrals*)
MW={Interpolation[Table[{(Ni-i)/Ni*2*bb-bb,W[(Ni-i)/Ni*2*bb-bb-I*Pi]},{i,0,Ni}]],Interpolation[Table[{(Ni-i)/Ni*2*bb-bb,W[(Ni-i)/Ni*2*bb-bb]},{i,0,Ni}]],Interpolation[Table[{(Ni-i)/Ni*2*bb-bb,W[(Ni-i)/Ni*2*bb-bb+I*Pi]},{i,0,Ni}]]};


(*******************************************************************)
(**********Two soliton form factors for general rapidities**********)
(*******************************************************************)

FF2[TT1_,TT2_]:=Module[{FFs,T1,T2},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];

(*Generating interpolation functions of the integrands*)
WI11=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T1]},{j,0,Ni}]]; (*W (x-Subscript[\[CapitalTheta], 1])*)
WI12=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T1)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 1]-x)*)
WI21=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T2]},{j,0,Ni}]];(*W (x-Subscript[\[CapitalTheta], 2])*)
WI22=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T2)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 2]-x)*)

(*Generating asymptotic series of the integrands*)
Dume=SHI[Iau,-T1];
hW02=PRO[Dume,SHI[Iau,-T2]];
hW11=PRO[SHI[Iau\[Conjugate],-T2],Dume];
hW20=PRO[SHI[Iau\[Conjugate],-T1],SHI[Iau\[Conjugate],-T2]];

hW02=NPRO[{1,A},hW02]; (*Asymptotic series of the integrand of Subscript[I, 02,k]*)
hW11=NPRO[{1,A},hW11]; (*Asymptotic series of the integrand of Subscript[I, 11,k]*)
hW20=NPRO[{1,A},hW20]; (*Asymptotic series of the integrand of Subscript[I, 20,k]*)

(*Calculation of Subscript[I, 02]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]>-Pi/2,Exp[A*(T2+I*Pi/2)]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[A*(T1+I*Pi/2)]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2-p[n])]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1-p[n])]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I02=AInt2[hW02]+Poles;
FunW[x_]:=Exp[A*x]*WI22[x]*WI12[x];
I02=I02+NIntegrate[FunW[x],{x,aa,bb}];

(*Calculation of Subscript[I, 11]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]<Pi/2,Exp[A*(T2-I*Pi/2)]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[A*(T1+I*Pi/2)]*W[-T2+T1+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2+p[n])]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1-p[n])]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I11=AInt2[hW11]+Poles;
FunW[x_]:=Exp[A*x]*WI21[x]*WI12[x];
I11=I11+NIntegrate[FunW[x],{x,aa,bb}];

(*Calculation of Subscript[I, 20]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]<Pi/2,Exp[A*(T2-I*Pi/2)]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[A*(T1-I*Pi/2)]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2+p[n])]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1+p[n])]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I20=AInt2[hW20]+Poles;
FunW[x_]:=Exp[A*x]*WI21[x]*WI11[x];
I20=I20+NIntegrate[FunW[x],{x,aa,bb}];

(* Assembly of form form factors *)
Ipm=Exp[I*Pi*(1+1/\[Xi])/2]I02-Exp[-I*Pi*(1+1/\[Xi])/2]*I11;
Imp=Exp[I*Pi*(1+1/\[Xi])/2]I11-Exp[-I*Pi*(1+1/\[Xi])/2]*I20;
Gss=I/8/Pi*C2/C1*G[T1-T2];

FF2pm=Ipm*Exp[-A*T2]*Exp[aover\[Beta]*(-T2+T1)]*Gss;
FF2mp=Imp*Exp[-A*T1]*Exp[aover\[Beta]*(+T2-T1)]*Gss;

FFs[[iii]]={FF2pm,FF2mp};
];FFs
];


(*******************************************************************)
(**********Four soliton form factors for general rapidities*********)
(*******************************************************************)

FF4[TT1_,TT2_,TT3_,TT4_]:=Module[{FFs,T1,T2,T3,T4},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];
T3=TT3[[iii]];
T4=TT4[[iii]];

(*Generating interpolation functions of the integrands*)
WI11=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T1]},{j,0,Ni}]]; (*W (x-Subscript[\[CapitalTheta], 1])*)
WI12=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T1)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 1]-x)*)
WI21=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T2]},{j,0,Ni}]];(*W (x-Subscript[\[CapitalTheta], 2])*)
WI22=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T2)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 2]-x)*)
WI31=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T3]},{j,0,Ni}]];(*W (x-Subscript[\[CapitalTheta], 3])*)
WI32=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T3)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 3]-x)*)
WI41=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T4]},{j,0,Ni}]];(*W (x-Subscript[\[CapitalTheta], 4])*)
WI42=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T4)]},{j,0,Ni}]]; (*W (Subscript[\[CapitalTheta], 4]-x)*)

(*Generating asymptotic series of the integrands*)
Dume=SHI[Iau,-T1];
Dumm=PRO[PRO[SHI[Iau\[Conjugate],-T2],SHI[Iau\[Conjugate],-T3]],SHI[Iau\[Conjugate],-T4]];
hW40=PRO[SHI[Iau\[Conjugate],-T1],Dumm];
hW31=PRO[Dume,Dumm];
Dume1=PRO[Dume,SHI[Iau,-T2]];
hW22=PRO[PRO[Dume1,SHI[Iau\[Conjugate],-T3]],SHI[Iau\[Conjugate],-T4]];
Dume2=PRO[Dume1,SHI[Iau,-T3]];
hW13=PRO[Dume2,SHI[Iau\[Conjugate],-T4]];
hW04=PRO[Dume2,SHI[Iau,-T4]];

hW04=NPRO[{1,A+alphaG4},hW04]; (*Asymptotic series of the integrand of Subscript[I, 04,k]*)
hW13=NPRO[{1,A+alphaG4},hW13]; (*Asymptotic series of the integrand of Subscript[I, 13,k]*)
hW22=NPRO[{1,A+alphaG4},hW22]; (*Asymptotic series of the integrand of Subscript[I, 22,k]*)
hW31=NPRO[{1,A+alphaG4},hW31]; (*Asymptotic series of the integrand of Subscript[I, 31,k]*)
hW40=NPRO[{1,A+alphaG4},hW40]; (*Asymptotic series of the integrand of Subscript[I, 40,k]*)

(*Calculation of Subscript[I, 04,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]>-Pi/2,Exp[(A+alphaG4)*(T4+I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG4)*(T3+I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4-p[n])]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3-p[n])]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I04=AInt4[hW04]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI42[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<5,inde++,
I04[[inde]]=I04[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Calculation of Subscript[I, 13,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T3-T4+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG4)*(T3+I*Pi/2)]*W[T3-T4+I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T2-T4+I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T3-T4-p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3-p[n])]*W[T3-T4-p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T2-T4-p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I13=AInt4[hW13]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI41[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<5,inde++,
I13[[inde]]=I13[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Calculation of Subscript[I, 22,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<+Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T2-T4+I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T2-T3-p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T2-T4-p[n]]*W[T2-T3-p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I22=AInt4[hW22]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI41[x]*WI31[x]*WI22[x]*WI12[x];
For[inde=1,inde<5,inde++,
I22[[inde]]=I22[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Calculation of Subscript[I, 31,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<+Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]<+Pi/2,Exp[(A+alphaG4)*(T2-I*Pi/2)]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T1-T2+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2+p[n])]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I31=AInt4[hW31]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI41[x]*WI31[x]*WI21[x]*WI12[x];
For[inde=1,inde<5,inde++,
I31[[inde]]=I31[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Calculation of Subscript[I, 40,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T4-T1-I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T3-T1-I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG4)*(T2-I*Pi/2)]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[(A+alphaG4)*(T1-I*Pi/2)]*W[T1-T4-I*Pi/2]*W[T1-T3-I*Pi/2]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T4-T1+p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T3-T1+p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2+p[n])]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1+p[n])]*W[T1-T4+p[n]]*W[T1-T3+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I40=AInt4[hW40]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI41[x]*WI31[x]*WI21[x]*WI11[x];
For[inde=1,inde<5,inde++,
I40[[inde]]=I40[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(* Assembly of form form factors *)
Immpp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I22,I31]-IPR4[I22,I40]-IPR4[I31,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I31,I40];
Ipmpm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I22]-IPR4[I13,I22]-IPR4[I04,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I31];
Impmp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I13,I31]-IPR4[I22,I31]-IPR4[I13,I40]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I22,I40];
Ipmmp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I13,I22]-IPR4[I22,I22]-IPR4[I13,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I22,I31];
Imppm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I31]-IPR4[I13,I31]-IPR4[I04,I40]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I40];
Ippmm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I13]-IPR4[I13,I13]-IPR4[I04,I22]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I22];
Gss=1/4/Pi^2*C2^3*\[Xi]/16/16/C1^2*G[T3-T4]*G[T2-T4]*G[T1-T4]*G[T2-T3]*G[T1-T3]*G[T1-T2];

FF4mmpp=Immpp*Exp[-A*(T1+T2)]*Exp[aover\[Beta]*(+T4+T3-T2-T1)]*Gss;
FF4pmpm=Ipmpm*Exp[-A*(T4+T2)]*Exp[aover\[Beta]*(-T4+T3-T2+T1)]*Gss;
FF4mpmp=Impmp*Exp[-A*(T1+T3)]*Exp[aover\[Beta]*(+T4-T3+T2-T1)]*Gss;
FF4pmmp=Ipmmp*Exp[-A*(T3+T2)]*Exp[aover\[Beta]*(+T4-T3-T2+T1)]*Gss;
FF4mppm=Imppm*Exp[-A*(T1+T4)]*Exp[aover\[Beta]*(-T4+T3+T2-T1)]*Gss;
FF4ppmm=Ippmm*Exp[-A*(T3+T4)]*Exp[aover\[Beta]*(-T4-T3+T2+T1)]*Gss;

FFs[[iii]]={FF4mmpp,FF4mpmp,FF4pmmp,FF4mppm,FF4pmpm,FF4ppmm};
];FFs
];


(*******************************************************************)
(*********Six soliton form factors for general rapidities***********)
(*******************************************************************)

FF6[TT1_,TT2_,TT3_,TT4_,TT5_,TT6_]:=Module[{FFs,T1,T2,T3,T4,T5,T6},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];
T3=TT3[[iii]];
T4=TT4[[iii]];
T5=TT5[[iii]];
T6=TT6[[iii]];

(*Generating interpolation functions for the integrals*)
WI11=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T1]},{j,0,Ni}]];
WI12=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T1)]},{j,0,Ni}]];
WI21=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T2]},{j,0,Ni}]];
WI22=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T2)]},{j,0,Ni}]];
WI31=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T3]},{j,0,Ni}]];
WI32=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T3)]},{j,0,Ni}]];
WI41=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T4]},{j,0,Ni}]];
WI42=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T4)]},{j,0,Ni}]];
WI51=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T5]},{j,0,Ni}]];
WI52=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T5)]},{j,0,Ni}]];
WI61=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[(Ni-j)/Ni*(bb-aa)+aa-T6]},{j,0,Ni}]];
WI62=Interpolation[Table[{(Ni-j)/Ni*(bb-aa)+aa,W[-((Ni-j)/Ni*(bb-aa)+aa-T6)]},{j,0,Ni}]];

(*Generating asymptotic series*)
Dummy=PRO[PRO[SHI[Iau\[Conjugate],-T6],SHI[Iau\[Conjugate],-T5]],SHI[Iau\[Conjugate],-T4]];
Dummy2=PRO[SHI[Iau\[Conjugate],-T6],SHI[Iau\[Conjugate],-T5]];
Dummy3=PRO[Dummy2,SHI[Iau\[Conjugate],-T4]];
Dummy4=PRO[Dummy3,SHI[Iau\[Conjugate],-T3]];
Dummy5=PRO[Dummy4,SHI[Iau\[Conjugate],-T2]];
Dum2=PRO[SHI[Iau,-T1],SHI[Iau,-T2]];
Dum22=PRO[Dum2,SHI[Iau,-T3]];
Dum222=PRO[Dum22,SHI[Iau,-T4]];
Dum2222=PRO[Dum222,SHI[Iau,-T5]];
hW06=NPRO[{1,A+alphaG6},PRO[Dum2222,SHI[Iau,-T6]]]; (*Asymptotic series of the integrand of Subscript[I, 06,k]*)
hW15=NPRO[{1,A+alphaG6},PRO[Dum2222,SHI[Iau\[Conjugate],-T6]]]; (*Asymptotic series of the integrand of Subscript[I, 15,k]*)
hW24=NPRO[{1,A+alphaG6},PRO[Dummy2,Dum222]]; (*Asymptotic series of the integrand of Subscript[I, 24,k]*)
hW33=NPRO[{1,A+alphaG6},PRO[PRO[PRO[Dummy,SHI[Iau,-T3]],SHI[Iau,-T2]],SHI[Iau,-T1]]]; (*Asymptotic series of the integrand of Subscript[I, 33,k]*)
hW42=NPRO[{1,A+alphaG6},PRO[Dummy4,Dum2]]; (*Asymptotic series of the integrand of Subscript[I, 42,k]*)
hW51=NPRO[{1,A+alphaG6},PRO[Dummy5,SHI[Iau,-T1]]]; (*Asymptotic series of the integrand of Subscript[I, 51,k]*)
hW60=NPRO[{1,A+alphaG6},PRO[Dummy5,SHI[Iau\[Conjugate],-T1]]]; (*Asymptotic series of the integrand of Subscript[I, 60,k]*)

(*Subscript[I, 06,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]>-Pi/2,Exp[(A+alphaG6)*(T6+I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T4-T6-I*Pi/2]*W[T3-T6-I*Pi/2]*W[T2-T6-I*Pi/2]*W[T1-T6-I*Pi/2],0]+If[Im[T5]>-Pi/2,Exp[(A+alphaG6)*(T5+I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T1-T5-I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T6-T4-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T6-T3-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T6-T2-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T6-T1-I*Pi/2]*W[T5-T1-I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6-p[n])]*W[T5-T6+p[n]]*W[T4-T6+p[n]]*W[T3-T6+p[n]]*W[T2-T6+p[n]]*W[T1-T6+p[n]],{n,1,Floor[(Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5-p[n])]*W[T6-T5+p[n]]*W[T4-T5+p[n]]*W[T3-T5+p[n]]*W[T2-T5+p[n]]*W[T1-T5+p[n]],{n,1,Floor[(Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T6-T4+p[n]]*W[T5-T4+p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T6-T3+p[n]]*W[T5-T3+p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T6-T2+p[n]]*W[T5-T2+p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T6-T1+p[n]]*W[T5-T1+p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I06=AInt6[hW06]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI62[x]*WI52[x]*WI42[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<10,inde++,
I06[[inde]]=I06[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 15,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T5-T6+I*Pi/2]*W[T4-T6+I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]>-Pi/2,Exp[(A+alphaG6)*(T5+I*Pi/2)]*W[T5-T6+I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T1-T5-I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T4-T6+I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T5-T3-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T5-T2-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T5-T1-I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T5-T6-p[n]]*W[T4-T6-p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5-p[n])]*W[T5-T6-p[n]]*W[T4-T5+p[n]]*W[T3-T5+p[n]]*W[T2-T5+p[n]]*W[T1-T5+p[n]],{n,1,Floor[(Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T4-T6-p[n]]*W[T5-T4+p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T5-T3+p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T5-T2+p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T5-T1+p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I15=AInt6[hW15]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI52[x]*WI42[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<10,inde++,
I15[[inde]]=I15[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 24,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T4-T6+I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T4-T5+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T4-T6+I*Pi/2]*W[T4-T5+I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T4-T6-p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T4-T5-p[n]]*W[T3-T5-p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T4-T6-p[n]]*W[T4-T5-p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T3-T5-p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I24=AInt6[hW24]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI51[x]*WI42[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<10,inde++,
I24[[inde]]=I24[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 33,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T5+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T4+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T3-T4+I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T3-T5-p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T3-T4-p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T3-T5-p[n]]*W[T3-T4-p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T2-T4-p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I33=AInt6[hW33]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI51[x]*WI41[x]*WI32[x]*WI22[x]*WI12[x];
For[inde=1,inde<10,inde++,
I33[[inde]]=I33[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 42,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T2-T3-p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T2-T4-p[n]]*W[T2-T3-p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I42=AInt6[hW42]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI51[x]*WI41[x]*WI31[x]*WI22[x]*WI12[x];
For[inde=1,inde<10,inde++,
I42[[inde]]=I42[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 51,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T6-T2-I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG6)*(T2-I*Pi/2)]*W[T2-T6-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T1-T2+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T6-T2+p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T5-T2+p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2+p[n])]*W[T2-T6+p[n]]*W[T2-T5+p[n]]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I51=AInt6[hW51]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI51[x]*WI41[x]*WI31[x]*WI21[x]*WI12[x];
For[inde=1,inde<10,inde++,
I51[[inde]]=I51[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 60,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T6-T2-I*Pi/2]*W[T6-T1-I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T5-T1-I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T4-T1-I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T3-T1-I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG6)*(T2-I*Pi/2)]*W[T2-T6-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[(A+alphaG6)*(T1-I*Pi/2)]*W[T1-T6-I*Pi/2]*W[T1-T5-I*Pi/2]*W[T1-T4-I*Pi/2]*W[T1-T3-I*Pi/2]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T6-T2+p[n]]*W[T6-T1+p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T5-T2+p[n]]*W[T5-T1+p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T4-T1+p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T3-T1+p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2+p[n])]*W[T2-T6+p[n]]*W[T2-T5+p[n]]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1+p[n])]*W[T1-T6+p[n]]*W[T1-T5+p[n]]*W[T1-T4+p[n]]*W[T1-T3+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I60=AInt6[hW60]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*WI61[x]*WI51[x]*WI41[x]*WI31[x]*WI21[x]*WI11[x];
For[inde=1,inde<10,inde++,
I60[[inde]]=I60[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

(* Assembly of form form factors *)
Gss=I/64^3/(2*Pi)^3*C2^6*\[Xi]^3/C1^3*G[T5-T6]*G[T4-T6]*G[T3-T6]*G[T2-T6]*G[T1-T6]*G[T4-T5]*G[T3-T5]*G[T2-T5]*G[T1-T5]*G[T3-T4]*G[T2-T4]*G[T1-T4]*G[T2-T3]*G[T1-T3]*G[T1-T2];

Ipppmmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I24]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I24]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I24]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I24]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I33];
Ippmpmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I42];
Ippmmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I42];
Ippmmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I42];
Ipmpmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I51];
Ipmppmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I51];
Ipmpmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I51];
Ipmmppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I51];
Ipmmpmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I51];
Ipmmmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I51];


Imppmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I60];
Impppmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I60];
Imppmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I60];
Impmppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I60];
Impmpmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I60];
Impmmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I60];
Immpppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I51,I60];
Immppmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I51,I60];
Immpmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I51,I60];
Immmppp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I42,I51,I60];

FF6pppmmm=Ipppmmm*Exp[-A*(T4+T5+T6)]*Exp[aover\[Beta]*(-T6-T5-T4+T3+T2+T1)]*Gss;
FF6ppmpmm=Ippmpmm*Exp[-A*(T3+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4-T3+T2+T1)]*Gss;
FF6ppmmpm=Ippmmpm*Exp[-A*(T3+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4-T3+T2+T1)]*Gss;
FF6ppmmmp=Ippmmmp*Exp[-A*(T3+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4-T3+T2+T1)]*Gss;
FF6pmpmpm=Ipmpmpm*Exp[-A*(T2+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4+T3-T2+T1)]*Gss;
FF6pmppmm=Ipmppmm*Exp[-A*(T2+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4+T3-T2+T1)]*Gss;
FF6pmpmmp=Ipmpmmp*Exp[-A*(T2+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4+T3-T2+T1)]*Gss;
FF6pmmppm=Ipmmppm*Exp[-A*(T2+T3+T6)]*Exp[aover\[Beta]*(-T6+T5+T4-T3-T2+T1)]*Gss;
FF6pmmpmp=Ipmmpmp*Exp[-A*(T2+T3+T5)]*Exp[aover\[Beta]*(+T6-T5+T4-T3-T2+T1)]*Gss;
FF6pmmmpp=Ipmmmpp*Exp[-A*(T2+T3+T4)]*Exp[aover\[Beta]*(+T6+T5-T4-T3-T2+T1)]*Gss;

FF6mppmpm=Imppmpm*Exp[-A*(T1+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4+T3+T2-T1)]*Gss;
FF6mpppmm=Impppmm*Exp[-A*(T1+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4+T3+T2-T1)]*Gss;
FF6mppmmp=Imppmmp*Exp[-A*(T1+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4+T3+T2-T1)]*Gss;
FF6mpmppm=Impmppm*Exp[-A*(T1+T3+T6)]*Exp[aover\[Beta]*(-T6+T5+T4-T3+T2-T1)]*Gss;
FF6mpmpmp=Impmpmp*Exp[-A*(T1+T3+T5)]*Exp[aover\[Beta]*(+T6-T5+T4-T3+T2-T1)]*Gss;
FF6mpmmpp=Impmmpp*Exp[-A*(T1+T3+T4)]*Exp[aover\[Beta]*(+T6+T5-T4-T3+T2-T1)]*Gss;
FF6mmpppm=Immpppm*Exp[-A*(T1+T2+T6)]*Exp[aover\[Beta]*(-T6+T5+T4+T3-T2-T1)]*Gss;
FF6mmppmp=Immppmp*Exp[-A*(T1+T2+T5)]*Exp[aover\[Beta]*(+T6-T5+T4+T3-T2-T1)]*Gss;
FF6mmpmpp=Immpmpp*Exp[-A*(T1+T2+T4)]*Exp[aover\[Beta]*(+T6+T5-T4+T3-T2-T1)]*Gss;
FF6mmmppp=Immmppp*Exp[-A*(T1+T2+T3)]*Exp[aover\[Beta]*(+T6+T5+T4-T3-T2-T1)]*Gss;
FFs[[iii]]={FF6pppmmm,FF6ppmpmm,FF6ppmmpm,FF6ppmmmp,FF6pmpmpm,FF6pmppmm,FF6pmpmmp,FF6pmmppm,FF6pmmpmp,FF6pmmmpp,FF6mpppmm,FF6mppmpm,FF6mppmmp,FF6mpmppm,FF6mpmmpp,FF6mpmpmp,FF6mmpppm,FF6mmppmp,FF6mmpmpp,FF6mmmppp};
];FFs
];


(*******************************************************************)
(*********Two soliton form factors for physical rapidities**********)
(*******************************************************************)

FF2p[TT1_,TT2_]:=Module[{FFs,T1,T2},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];

IPIKp={Sign[Im[T1]]+2,Sign[Im[T2]]+2};
IPIKm={Sign[-Im[T1]]+2,Sign[-Im[T2]]+2};

(*Generating asymptotic series of the integrands*)
Dume=SHI[Iau,-T1];
hW02=PRO[Dume,SHI[Iau,-T2]];
hW11=PRO[SHI[Iau\[Conjugate],-T2],Dume];
hW20=PRO[SHI[Iau\[Conjugate],-T1],SHI[Iau\[Conjugate],-T2]];

hW02=NPRO[{1,A},hW02]; (*Asymptotic series of the integrand of Subscript[I, 02,k]*)
hW11=NPRO[{1,A},hW11]; (*Asymptotic series of the integrand of Subscript[I, 11,k]*)
hW20=NPRO[{1,A},hW20]; (*Asymptotic series of the integrand of Subscript[I, 20,k]*)

(*Calculation of Subscript[I, 02]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]>-Pi/2,Exp[A*(T2+I*Pi/2)]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[A*(T1+I*Pi/2)]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2-p[n])]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1-p[n])]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I02=AInt2[hW02]+Poles;
FunW[x_]:=Exp[A*x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
I02=I02+NIntegrate[FunW[x],{x,aa,bb}];

(*Calculation of Subscript[I, 11]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]<Pi/2,Exp[A*(T2-I*Pi/2)]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[A*(T1+I*Pi/2)]*W[-T2+T1+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2+p[n])]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1-p[n])]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I11=AInt2[hW11]+Poles;
FunW[x_]:=Exp[A*x]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKp[[1]]]][Re[T1]-x];
I11=I11+NIntegrate[FunW[x],{x,aa,bb}];

(*Calculation of Subscript[I, 20]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T2]<Pi/2,Exp[A*(T2-I*Pi/2)]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[A*(T1-I*Pi/2)]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[A*(T2+p[n])]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[A*(T1+p[n])]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I20=AInt2[hW20]+Poles;
FunW[x_]:=Exp[A*x]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKm[[1]]]][x-Re[T1]];
I20=I20+NIntegrate[FunW[x],{x,aa,bb}];

(* Assembly of form form factors *)
Ipm=Exp[I*Pi*(1+1/\[Xi])/2]I02-Exp[-I*Pi*(1+1/\[Xi])/2]*I11;
Imp=Exp[I*Pi*(1+1/\[Xi])/2]I11-Exp[-I*Pi*(1+1/\[Xi])/2]*I20;
Gss=I/8/Pi*C2/C1*G[T1-T2];

FF2pm=Ipm*Exp[-A*T2]*Exp[aover\[Beta]*(-T2+T1)]*Gss;
FF2mp=Imp*Exp[-A*T1]*Exp[aover\[Beta]*(+T2-T1)]*Gss;

FFs[[iii]]={FF2pm,FF2mp};
];FFs
];


(*******************************************************************)
(**********Four soliton form factors for physical rapidities********)
(*******************************************************************)

FF4p[TT1_,TT2_,TT3_,TT4_]:=Module[{FFs,T1,T2,T3,T4},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];
T3=TT3[[iii]];
T4=TT4[[iii]];

IPIKp={Sign[Im[T1]]+2,Sign[Im[T2]]+2,Sign[Im[T3]]+2,Sign[Im[T4]]+2};
IPIKm={Sign[-Im[T1]]+2,Sign[-Im[T2]]+2,Sign[-Im[T3]]+2,Sign[-Im[T4]]+2};

(*Generating asymptotic series*)
Dume=SHI[Iau,-T1];
Dumm=PRO[PRO[SHI[Iau\[Conjugate],-T2],SHI[Iau\[Conjugate],-T3]],SHI[Iau\[Conjugate],-T4]];
hW40=PRO[SHI[Iau\[Conjugate],-T1],Dumm];
hW31=PRO[Dume,Dumm];
Dume1=PRO[Dume,SHI[Iau,-T2]];
hW22=PRO[PRO[Dume1,SHI[Iau\[Conjugate],-T3]],SHI[Iau\[Conjugate],-T4]];
Dume2=PRO[Dume1,SHI[Iau,-T3]];
hW13=PRO[Dume2,SHI[Iau\[Conjugate],-T4]];
hW04=PRO[Dume2,SHI[Iau,-T4]];

hW04=NPRO[{1,A+alphaG4},hW04]; (*Asymptotic series of the integrand of Subscript[I, 04,k]*)
hW13=NPRO[{1,A+alphaG4},hW13]; (*Asymptotic series of the integrand of Subscript[I, 13,k]*)
hW22=NPRO[{1,A+alphaG4},hW22]; (*Asymptotic series of the integrand of Subscript[I, 22,k]*)
hW31=NPRO[{1,A+alphaG4},hW31]; (*Asymptotic series of the integrand of Subscript[I, 31,k]*)
hW40=NPRO[{1,A+alphaG4},hW40]; (*Asymptotic series of the integrand of Subscript[I, 40,k]*)

(*Subscript[I, 04,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]>-Pi/2,Exp[(A+alphaG4)*(T4+I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG4)*(T3+I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4-p[n])]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3-p[n])]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I04=AInt4[hW04]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKp[[4]]]][Re[T4]-x]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<5,inde++,
I04[[inde]]=I04[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 13,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T3-T4+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG4)*(T3+I*Pi/2)]*W[T3-T4+I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T2-T4+I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T3-T4-p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3-p[n])]*W[T3-T4-p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T2-T4-p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I13=AInt4[hW13]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<5,inde++,
I13[[inde]]=I13[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 22,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<+Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG4)*(T2+I*Pi/2)]*W[T2-T4+I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T2-T3-p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2-p[n])]*W[T2-T4-p[n]]*W[T2-T3-p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I22=AInt4[hW22]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<5,inde++,
I22[[inde]]=I22[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 31,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<+Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<+Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]<+Pi/2,Exp[(A+alphaG4)*(T2-I*Pi/2)]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG4)*(T1+I*Pi/2)]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T1-T2+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2+p[n])]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1-p[n])]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I31=AInt4[hW31]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<5,inde++,
I31[[inde]]=I31[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(*Subscript[I, 40,k]*)
Poles=4*Pi/Sqrt[C2]*(If[Im[T4]<Pi/2,Exp[(A+alphaG4)*(T4-I*Pi/2)]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T4-T1-I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG4)*(T3-I*Pi/2)]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T3-T1-I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG4)*(T2-I*Pi/2)]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[(A+alphaG4)*(T1-I*Pi/2)]*W[T1-T4-I*Pi/2]*W[T1-T3-I*Pi/2]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG4)*(T4+p[n])]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T4-T1+p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T3+p[n])]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T3-T1+p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T2+p[n])]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG4)*(T1+p[n])]*W[T1-T4+p[n]]*W[T1-T3+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I40=AInt4[hW40]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKm[[1]]]][x-Re[T1]];
For[inde=1,inde<5,inde++,
I40[[inde]]=I40[[inde]]+NIntegrate[FunW[alphaG4[[inde]],x],{x,aa,bb}];
];

(* Assembly of form form factors *)
Immpp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I22,I31]-IPR4[I22,I40]-IPR4[I31,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I31,I40];
Ipmpm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I22]-IPR4[I13,I22]-IPR4[I04,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I31];
Impmp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I13,I31]-IPR4[I22,I31]-IPR4[I13,I40]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I22,I40];
Ipmmp=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I13,I22]-IPR4[I22,I22]-IPR4[I13,I31]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I22,I31];
Imppm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I31]-IPR4[I13,I31]-IPR4[I04,I40]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I40];
Ippmm=Exp[I*Pi*(1+1/\[Xi])]*IPR4[I04,I13]-IPR4[I13,I13]-IPR4[I04,I22]+Exp[-I*Pi*(1+1/\[Xi])]*IPR4[I13,I22];
Gss=1/4/Pi^2*C2^3*\[Xi]/16/16/C1^2*G[T3-T4]*G[T2-T4]*G[T1-T4]*G[T2-T3]*G[T1-T3]*G[T1-T2];

FF4mmpp=Immpp*Exp[-A*(T1+T2)]*Exp[aover\[Beta]*(T4+T3-T2-T1)]*Gss;
FF4pmpm=Ipmpm*Exp[-A*(T4+T2)]*Exp[aover\[Beta]*(-T4+T3-T2+T1)]*Gss;
FF4mpmp=Impmp*Exp[-A*(T1+T3)]*Exp[aover\[Beta]*(+T4-T3+T2-T1)]*Gss;
FF4pmmp=Ipmmp*Exp[-A*(T3+T2)]*Exp[aover\[Beta]*(+T4-T3-T2+T1)]*Gss;
FF4mppm=Imppm*Exp[-A*(T1+T4)]*Exp[aover\[Beta]*(-T4+T3+T2-T1)]*Gss;
FF4ppmm=Ippmm*Exp[-A*(T3+T4)]*Exp[aover\[Beta]*(-T4-T3+T2+T1)]*Gss;
FFs[[iii]]={FF4mmpp,FF4mpmp,FF4pmmp,FF4mppm,FF4pmpm,FF4ppmm};
];FFs
];


(*******************************************************************)
(**********Six soliton form factors for physical rapidities*********)
(*******************************************************************)

FF6p[TT1_,TT2_,TT3_,TT4_,TT5_,TT6_]:=Module[{FFs,T1,T2,T3,T4,T5,T6},FFs=Table[0,{j,1,Length[TT1]}];
For[iii=1,iii<Length[TT1]+1,iii=iii+1,
T1=TT1[[iii]];
T2=TT2[[iii]];
T3=TT3[[iii]];
T4=TT4[[iii]];
T5=TT5[[iii]];
T6=TT6[[iii]];

IPIKp={Sign[Im[T1]]+2,Sign[Im[T2]]+2,Sign[Im[T3]]+2,Sign[Im[T4]]+2,Sign[Im[T5]]+2,Sign[Im[T6]]+2};
IPIKm={Sign[-Im[T1]]+2,Sign[-Im[T2]]+2,Sign[-Im[T3]]+2,Sign[-Im[T4]]+2,Sign[-Im[T5]]+2,Sign[-Im[T6]]+2};

Dummy=PRO[PRO[SHI[Iau\[Conjugate],-T6],SHI[Iau\[Conjugate],-T5]],SHI[Iau\[Conjugate],-T4]];
Dummy2=PRO[SHI[Iau\[Conjugate],-T6],SHI[Iau\[Conjugate],-T5]];
Dummy3=PRO[Dummy2,SHI[Iau\[Conjugate],-T4]];
Dummy4=PRO[Dummy3,SHI[Iau\[Conjugate],-T3]];
Dummy5=PRO[Dummy4,SHI[Iau\[Conjugate],-T2]];
Dum2=PRO[SHI[Iau,-T1],SHI[Iau,-T2]];
Dum22=PRO[Dum2,SHI[Iau,-T3]];
Dum222=PRO[Dum22,SHI[Iau,-T4]];
Dum2222=PRO[Dum222,SHI[Iau,-T5]];
hW06=PRO[Dum2222,SHI[Iau,-T6]];
hW15=PRO[Dum2222,SHI[Iau\[Conjugate],-T6]];
hW24=PRO[Dummy2,Dum222];
hW33=PRO[PRO[PRO[Dummy,SHI[Iau,-T3]],SHI[Iau,-T2]],SHI[Iau,-T1]];
hW42=PRO[Dummy4,Dum2];
hW51=PRO[Dummy5,SHI[Iau,-T1]];
hW60=PRO[Dummy5,SHI[Iau\[Conjugate],-T1]];

Dum=NPRO[{1,A+alphaG6},hW06];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]>-Pi/2,Exp[(A+alphaG6)*(T6+I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T4-T6-I*Pi/2]*W[T3-T6-I*Pi/2]*W[T2-T6-I*Pi/2]*W[T1-T6-I*Pi/2],0]+If[Im[T5]>-Pi/2,Exp[(A+alphaG6)*(T5+I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T1-T5-I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T6-T4-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T6-T3-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T6-T2-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T6-T1-I*Pi/2]*W[T5-T1-I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6-p[n])]*W[T5-T6+p[n]]*W[T4-T6+p[n]]*W[T3-T6+p[n]]*W[T2-T6+p[n]]*W[T1-T6+p[n]],{n,1,Floor[(Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5-p[n])]*W[T6-T5+p[n]]*W[T4-T5+p[n]]*W[T3-T5+p[n]]*W[T2-T5+p[n]]*W[T1-T5+p[n]],{n,1,Floor[(Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T6-T4+p[n]]*W[T5-T4+p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T6-T3+p[n]]*W[T5-T3+p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T6-T2+p[n]]*W[T5-T2+p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T6-T1+p[n]]*W[T5-T1+p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I06=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKp[[6]]]][Re[T6]-x]*MW[[IPIKp[[5]]]][Re[T5]-x]*MW[[IPIKp[[4]]]][Re[T4]-x]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I06[[inde]]=I06[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW15];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T5-T6+I*Pi/2]*W[T4-T6+I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]>-Pi/2,Exp[(A+alphaG6)*(T5+I*Pi/2)]*W[T5-T6+I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T1-T5-I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T4-T6+I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T5-T3-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T5-T2-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T5-T1-I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T5-T6-p[n]]*W[T4-T6-p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5-p[n])]*W[T5-T6-p[n]]*W[T4-T5+p[n]]*W[T3-T5+p[n]]*W[T2-T5+p[n]]*W[T1-T5+p[n]],{n,1,Floor[(Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T4-T6-p[n]]*W[T5-T4+p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T5-T3+p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T5-T2+p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T5-T1+p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I15=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKp[[5]]]][Re[T5]-x]*MW[[IPIKp[[4]]]][Re[T4]-x]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I15[[inde]]=I15[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW24];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T4-T6+I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T4-T5+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]>-Pi/2,Exp[(A+alphaG6)*(T4+I*Pi/2)]*W[T4-T6+I*Pi/2]*W[T4-T5+I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T1-T4-I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T4-T2-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T4-T1-I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T4-T6-p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T4-T5-p[n]]*W[T3-T5-p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4-p[n])]*W[T4-T6-p[n]]*W[T4-T5-p[n]]*W[T3-T4+p[n]]*W[T2-T4+p[n]]*W[T1-T4+p[n]],{n,1,Floor[(Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T3-T5-p[n]]*W[T4-T3+p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T4-T2+p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T4-T1+p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I24=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKm[[5]]]][x-Re[T5]]*MW[[IPIKp[[4]]]][Re[T4]-x]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I24[[inde]]=I24[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW33];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T3-T6+I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T3-T5+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T3-T4+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]>-Pi/2,Exp[(A+alphaG6)*(T3+I*Pi/2)]*W[T3-T6+I*Pi/2]*W[T3-T5+I*Pi/2]*W[T3-T4+I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T3-I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T3-T1-I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T3-T6-p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T3-T5-p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T3-T4-p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3-p[n])]*W[T3-T6-p[n]]*W[T3-T5-p[n]]*W[T3-T4-p[n]]*W[T2-T3+p[n]]*W[T1-T3+p[n]],{n,1,Floor[(Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T2-T4-p[n]]*W[T3-T2+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T3-T1+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I33=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKm[[5]]]][x-Re[T5]]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKp[[3]]]][Re[T3]-x]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I33[[inde]]=I33[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW42];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T2-T6+I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T2-T5+I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T2-T4+I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]>-Pi/2,Exp[(A+alphaG6)*(T2+I*Pi/2)]*W[T2-T6+I*Pi/2]*W[T2-T5+I*Pi/2]*W[T2-T4+I*Pi/2]*W[T2-T3+I*Pi/2]*W[T1-T2-I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T2-T1-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T2-T6-p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T2-T5-p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T2-T4-p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T2-T3-p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2-p[n])]*W[T2-T6-p[n]]*W[T2-T5-p[n]]*W[T2-T4-p[n]]*W[T2-T3-p[n]]*W[T1-T2+p[n]],{n,1,Floor[(Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T2-T1+p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I42=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKm[[5]]]][x-Re[T5]]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKp[[2]]]][Re[T2]-x]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I42[[inde]]=I42[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW51];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T6-T2-I*Pi/2]*W[T1-T6+I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T1-T5+I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T1-T4+I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T1-T3+I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG6)*(T2-I*Pi/2)]*W[T2-T6-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T1-T2+I*Pi/2],0]+If[Im[T1]>-Pi/2,Exp[(A+alphaG6)*(T1+I*Pi/2)]*W[T1-T6+I*Pi/2]*W[T1-T5+I*Pi/2]*W[T1-T4+I*Pi/2]*W[T1-T3+I*Pi/2]*W[T1-T2+I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T6-T2+p[n]]*W[T1-T6-p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T5-T2+p[n]]*W[T1-T5-p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T1-T4-p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T1-T3-p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2+p[n])]*W[T2-T6+p[n]]*W[T2-T5+p[n]]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T1-T2-p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1-p[n])]*W[T1-T6-p[n]]*W[T1-T5-p[n]]*W[T1-T4-p[n]]*W[T1-T3-p[n]]*W[T1-T2-p[n]],{n,1,Floor[(Im[T1]/Pi+1/2)/\[Xi]]}]);
I51=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKm[[5]]]][x-Re[T5]]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKp[[1]]]][Re[T1]-x];
For[inde=1,inde<10,inde++,
I51[[inde]]=I51[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Dum=NPRO[{1,A+alphaG6},hW60];
Poles=4*Pi/Sqrt[C2]*(If[Im[T6]<Pi/2,Exp[(A+alphaG6)*(T6-I*Pi/2)]*W[T6-T5-I*Pi/2]*W[T6-T4-I*Pi/2]*W[T6-T3-I*Pi/2]*W[T6-T2-I*Pi/2]*W[T6-T1-I*Pi/2],0]+If[Im[T5]<Pi/2,Exp[(A+alphaG6)*(T5-I*Pi/2)]*W[T5-T6-I*Pi/2]*W[T5-T4-I*Pi/2]*W[T5-T3-I*Pi/2]*W[T5-T2-I*Pi/2]*W[T5-T1-I*Pi/2],0]+If[Im[T4]<Pi/2,Exp[(A+alphaG6)*(T4-I*Pi/2)]*W[T4-T6-I*Pi/2]*W[T4-T5-I*Pi/2]*W[T4-T3-I*Pi/2]*W[T4-T2-I*Pi/2]*W[T4-T1-I*Pi/2],0]+If[Im[T3]<Pi/2,Exp[(A+alphaG6)*(T3-I*Pi/2)]*W[T3-T6-I*Pi/2]*W[T3-T5-I*Pi/2]*W[T3-T4-I*Pi/2]*W[T3-T2-I*Pi/2]*W[T3-T1-I*Pi/2],0]+If[Im[T2]<Pi/2,Exp[(A+alphaG6)*(T2-I*Pi/2)]*W[T2-T6-I*Pi/2]*W[T2-T5-I*Pi/2]*W[T2-T4-I*Pi/2]*W[T2-T3-I*Pi/2]*W[T2-T1-I*Pi/2],0]+If[Im[T1]<Pi/2,Exp[(A+alphaG6)*(T1-I*Pi/2)]*W[T1-T6-I*Pi/2]*W[T1-T5-I*Pi/2]*W[T1-T4-I*Pi/2]*W[T1-T3-I*Pi/2]*W[T1-T2-I*Pi/2],0])+2*Pi*I*(Sum[r[n]*Exp[(A+alphaG6)*(T6+p[n])]*W[T6-T5+p[n]]*W[T6-T4+p[n]]*W[T6-T3+p[n]]*W[T6-T2+p[n]]*W[T6-T1+p[n]],{n,1,Floor[(-Im[T6]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T5+p[n])]*W[T5-T6+p[n]]*W[T5-T4+p[n]]*W[T5-T3+p[n]]*W[T5-T2+p[n]]*W[T5-T1+p[n]],{n,1,Floor[(-Im[T5]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T4+p[n])]*W[T4-T6+p[n]]*W[T4-T5+p[n]]*W[T4-T3+p[n]]*W[T4-T2+p[n]]*W[T4-T1+p[n]],{n,1,Floor[(-Im[T4]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T3+p[n])]*W[T3-T6+p[n]]*W[T3-T5+p[n]]*W[T3-T4+p[n]]*W[T3-T2+p[n]]*W[T3-T1+p[n]],{n,1,Floor[(-Im[T3]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T2+p[n])]*W[T2-T6+p[n]]*W[T2-T5+p[n]]*W[T2-T4+p[n]]*W[T2-T3+p[n]]*W[T2-T1+p[n]],{n,1,Floor[(-Im[T2]/Pi+1/2)/\[Xi]]}]+Sum[r[n]*Exp[(A+alphaG6)*(T1+p[n])]*W[T1-T6+p[n]]*W[T1-T5+p[n]]*W[T1-T4+p[n]]*W[T1-T3+p[n]]*W[T1-T2+p[n]],{n,1,Floor[(-Im[T1]/Pi+1/2)/\[Xi]]}]);
I60=AInt6[Dum]+Poles;
FunW[expo_,x_]:=Exp[(A+expo)*x]*MW[[IPIKm[[6]]]][x-Re[T6]]*MW[[IPIKm[[5]]]][x-Re[T5]]*MW[[IPIKm[[4]]]][x-Re[T4]]*MW[[IPIKm[[3]]]][x-Re[T3]]*MW[[IPIKm[[2]]]][x-Re[T2]]*MW[[IPIKm[[1]]]][x-Re[T1]];
For[inde=1,inde<10,inde++,
I60[[inde]]=I60[[inde]]+NIntegrate[FunW[alphaG6[[inde]],x],{x,aa,bb}];
];

Gss=I/64^3/(2*Pi)^3*C2^6*\[Xi]^3/C1^3*G[T5-T6]*G[T4-T6]*G[T3-T6]*G[T2-T6]*G[T1-T6]*G[T4-T5]*G[T3-T5]*G[T2-T5]*G[T1-T5]*G[T3-T4]*G[T2-T4]*G[T1-T4]*G[T2-T3]*G[T1-T3]*G[T1-T2];

Ipppmmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I24]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I24]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I24]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I24]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I33];
Ippmpmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I42];
Ippmmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I42];
Ippmmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I33]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I33]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I33]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I42];
Ipmpmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I51];
Ipmppmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I51];
Ipmpmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I51];
Ipmmppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I51];
Ipmmpmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I51];
Ipmmmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I42]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I42]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I42]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I51];


Imppmpm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I60];
Impppmm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I15,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I15,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I15,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I60];
Imppmmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I24,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I24,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I24,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I60];
Impmppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I60];
Impmpmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I60];
Impmmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I33,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I33,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I33,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I60];
Immpppm=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I06,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I06,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I51,I60];
Immppmp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I15,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I15,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I51,I60];
Immpmpp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I24,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I24,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I51,I60];
Immmppp=Exp[3/2*I*Pi*(1+1/\[Xi])]*IPR6[I33,I42,I51]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I42,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I33,I51,I60]-Exp[I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I42,I51]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I42,I60]+Exp[-I*Pi/2*(1+1/\[Xi])]*IPR6[I42,I51,I51]-Exp[-3/2*I*Pi*(1+1/\[Xi])]*IPR6[I42,I51,I60];

FF6pppmmm=Ipppmmm*Exp[-A*(T4+T5+T6)]*Exp[aover\[Beta]*(-T6-T5-T4+T3+T2+T1)]*Gss;
FF6ppmpmm=Ippmpmm*Exp[-A*(T3+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4-T3+T2+T1)]*Gss;
FF6ppmmpm=Ippmmpm*Exp[-A*(T3+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4-T3+T2+T1)]*Gss;
FF6ppmmmp=Ippmmmp*Exp[-A*(T3+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4-T3+T2+T1)]*Gss;
FF6pmpmpm=Ipmpmpm*Exp[-A*(T2+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4+T3-T2+T1)]*Gss;
FF6pmppmm=Ipmppmm*Exp[-A*(T2+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4+T3-T2+T1)]*Gss;
FF6pmpmmp=Ipmpmmp*Exp[-A*(T2+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4+T3-T2+T1)]*Gss;
FF6pmmppm=Ipmmppm*Exp[-A*(T2+T3+T6)]*Exp[aover\[Beta]*(-T6+T5+T4-T3-T2+T1)]*Gss;
FF6pmmpmp=Ipmmpmp*Exp[-A*(T2+T3+T5)]*Exp[aover\[Beta]*(+T6-T5+T4-T3-T2+T1)]*Gss;
FF6pmmmpp=Ipmmmpp*Exp[-A*(T2+T3+T4)]*Exp[aover\[Beta]*(+T6+T5-T4-T3-T2+T1)]*Gss;

FF6mppmpm=Imppmpm*Exp[-A*(T1+T4+T6)]*Exp[aover\[Beta]*(-T6+T5-T4+T3+T2-T1)]*Gss;
FF6mpppmm=Impppmm*Exp[-A*(T1+T5+T6)]*Exp[aover\[Beta]*(-T6-T5+T4+T3+T2-T1)]*Gss;
FF6mppmmp=Imppmmp*Exp[-A*(T1+T4+T5)]*Exp[aover\[Beta]*(+T6-T5-T4+T3+T2-T1)]*Gss;
FF6mpmppm=Impmppm*Exp[-A*(T1+T3+T6)]*Exp[aover\[Beta]*(-T6+T5+T4-T3+T2-T1)]*Gss;
FF6mpmpmp=Impmpmp*Exp[-A*(T1+T3+T5)]*Exp[aover\[Beta]*(+T6-T5+T4-T3+T2-T1)]*Gss;
FF6mpmmpp=Impmmpp*Exp[-A*(T1+T3+T4)]*Exp[aover\[Beta]*(+T6+T5-T4-T3+T2-T1)]*Gss;
FF6mmpppm=Immpppm*Exp[-A*(T1+T2+T6)]*Exp[aover\[Beta]*(-T6+T5+T4+T3-T2-T1)]*Gss;
FF6mmppmp=Immppmp*Exp[-A*(T1+T2+T5)]*Exp[aover\[Beta]*(+T6-T5+T4+T3-T2-T1)]*Gss;
FF6mmpmpp=Immpmpp*Exp[-A*(T1+T2+T4)]*Exp[aover\[Beta]*(+T6+T5-T4+T3-T2-T1)]*Gss;
FF6mmmppp=Immmppp*Exp[-A*(T1+T2+T3)]*Exp[aover\[Beta]*(+T6+T5+T4-T3-T2-T1)]*Gss;
FFs[[iii]]={FF6pppmmm,FF6ppmpmm,FF6ppmmpm,FF6ppmmmp,FF6pmpmpm,FF6pmppmm,FF6pmpmmp,FF6pmmppm,FF6pmmpmp,FF6pmmmpp,FF6mpppmm,FF6mppmpm,FF6mppmmp,FF6mpmppm,FF6mpmmpp,FF6mpmpmp,FF6mmpppm,FF6mmppmp,FF6mmpmpp,FF6mmmppp};
];FFs
];
