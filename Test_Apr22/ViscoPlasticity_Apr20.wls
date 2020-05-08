#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Input::Initialization:: *)
Unprotect[Out];
$HistoryLength=0;
ParallelEvaluate[$HistoryLength=0];
<<NDSolve`FEM`
(*dir=NotebookDirectory[]
SetDirectory[dir]*)


(* ::Input::Initialization:: *)
ClearAll[PlotMeshBC]
Protect[ShowMesh,ShowNumbers,ShowBCs];
Options[PlotMeshBC]={ShowMesh->False,ShowNumbers->False,ShowBCs->False};
PlotMeshBC[DirichletPoints_,NeumannPoints_,OptionsPattern[]]:=
If[OptionValue[ShowMesh],
Block[{PltPoints,plt},
Switch[OptionValue[ShowBCs]
,"DirichletBC"
,PltPoints =Cases[DirichletPoints,{#,_}][[;;,2]]&/@Range[ndof];
plt = True;
,"NeumannBC"
,PltPoints =Cases[NeumannPoints,{#,_}][[;;,2]]&/@Range[ndof];
plt = True;
,False
,plt =False;];
Show[
Join[{mesh["Wireframe"]}
,
If[OptionValue[ShowNumbers]
,{mesh["Wireframe"["MeshElement" -> "MeshElements","MeshElementIDStyle"->Blue]]
,mesh["Wireframe"["MeshElement" -> "PointElements","MeshElementIDStyle"->Red]]},{}]
,
If[plt
,Switch[ndof
,2,{Graphics[{PointSize[Large],Orange,Point[Coords[[PltPoints[[1]]]]]}]
,Graphics[{PointSize[Large],Green,Point[Coords[[PltPoints[[2]]]]]}]}
,3,{Graphics3D[{PointSize[Large],Orange,Point[Coords[[PltPoints[[1]]]]]}]
,Graphics3D[{PointSize[Large],Green,Point[Coords[[PltPoints[[2]]]]]}]
,Graphics3D[{PointSize[Large],Purple,Opacity[0.3],Point[Coords[[PltPoints[[3]]]]]}]}
],{}]
]]],Null];

PrintBB[X_List]:=Block[{},
Print[Sequence@@(Style[#,Blue,Bold]&/@X)];
]
PrintRB[X_List]:=Block[{},
Print[Sequence@@(Style[#,Red,Bold]&/@X)];
]


(* ::Input::Initialization:: *)
ClearAll[DefineBCs];
DefineBCs[uVec_,tVec_,L_,CrackLen_]:=
Block[{tol=10^-5,IDArray},
DirichletPoints=Block[{Bttm,BttmRit,Rit,RitBttm,Tp,Nodes},
Bttm =Flatten@Position[Abs[Coords[[;;,2]]-0.0],x_/;x<tol];
BttmRit= Position[Coords[[Bttm,1]]-CrackLen,x_/;x>=tol];
Rit= Flatten@Position[Abs[Coords[[;;,1]]-L],x_/;x<tol];
RitBttm= Position[Abs[Coords[[Rit,2]]-0.0],x_/;x<tol];
Tp= Flatten@Position[Abs[Coords[[;;,2]]-L],x_/;x<tol];
If[Norm@Through[tVec[1,1,1]]<tol,
Nodes = Join[{1,#}&/@Extract[Rit,RitBttm],{2,#}&/@Extract[Bttm,BttmRit],{2,#}&/@Tp]
,Nodes = Join[{1,#}&/@Extract[Rit,RitBttm],{2,#}&/@Extract[Bttm,BttmRit]]
]
];
DirichletDof = Sort[(DirichletPoints[[;;,2]]-1)*ndof+DirichletPoints[[;;,1]]];
NeumannPoints=Block[{Tp,Nodes},
Tp=Flatten@Position[Abs[Coords[[;;,2]]-L],x_/;x<tol];
Nodes =  {2,#}&/@Tp
];
NeumannDof= Sort[(NeumannPoints[[;;,2]]-1)*ndof+NeumannPoints[[;;,1]]];
Edges =Extract[mesh["BoundaryElements"][[1,1]],Position[Map[Norm@(#-{0,1})&,mesh["BoundaryNormals"][[1]]],x_/;x<tol]];
DirichletVals=uVec[[#[[1]]]][Coords[[#[[2]]]]]&/@DirichletPoints;
NeumannVals=tVec[[#[[1]]]][Coords[[#[[2]]]]]&/@NeumannPoints;
IDArray=Range[ndof*nnp];
IDMat=Transpose[ArrayReshape[IDArray,{nnp,ndof}]];
IDno=Complement[IDArray,DirichletDof];
]


(* ::Input::Initialization:: *)
DefineGaussAndSFInfo[ElementType_,integrationOrder_,elementOrder_]:=
Block[{},
GuassPointsNatural=ElementIntegrationPoints[ToExpression[ElementType],integrationOrder];
GaussIndex=AssociationMap[Position[GuassPointsNatural,#][[1,1]]&,GuassPointsNatural];
GuassWeights=ElementIntegrationWeights[ToExpression[ElementType],integrationOrder];
NMat=ElementShapeFunction[ToExpression[ElementType],elementOrder];
dN= ElementShapeFunctionDerivative[ToExpression[ElementType],elementOrder];
];
GuassIntegrate[coord_List,f0_]:=
Block[{f=f0,GuassPointsSpatial},
GuassPointsSpatial=Apply[NMat,GuassPointsNatural,2].coord;
GuassWeights.MapThread[f,{GuassPointsNatural,GuassPointsSpatial}]
];


(* ::Input::Initialization:: *)
stress[e0_,dt_,BMat:_,ELEdu:_,ElTypId_,\[Xi]_List]:=
Block[
{e=e0,gi,d\[Epsilon],de,S,\[Sigma]equiv,sol\[Epsilon]p,\[CapitalDelta]\[Epsilon]plas,\[Beta],\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]},
{\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]}=MaterialProperty;
gi=GaussIndex@\[Xi];
d\[Epsilon]=ConstantArray[0.0,{3,3}];
d\[Epsilon][[;;ndof,;;ndof]]=((BMat[\[Xi]].ELEdu)+Transpose[(BMat[\[Xi]].ELEdu)])/2;
de=(d\[Epsilon]-Tr[d\[Epsilon]]/3 IdentityMatrix[3]);
S =(\[Sigma][[ElTypId,e,gi]]-Tr[\[Sigma][[ElTypId,e,gi]]]/3 IdentityMatrix[3])+\[CapitalEpsilon]/(1+\[Nu]) de;
\[Sigma]equiv=Sqrt[3./2.]Norm[S,"Frobenius"];
ClearAll[x];
sol\[Epsilon]p=NSolve[\[Sigma]equiv/Y-(3\[CapitalEpsilon])/(2 Y (1+\[Nu])) x-(1+(\[Epsilon]plas[[ElTypId,e,gi]]+x)/\[Epsilon]0)^(1./\[ScriptN]) (x/(dt \[Epsilon]dot0 (*Exp[-Q/k T]*)))^(1./\[ScriptM])==0&&x>=0,x,Reals];
\[CapitalDelta]\[Epsilon]plas=x/.sol\[Epsilon]p[[1]];
\[Beta]=If[\[Sigma]equiv>0,1-(3 \[CapitalEpsilon] \[CapitalDelta]\[Epsilon]plas)/(2(1+\[Nu])\[Sigma]equiv),1.0];
\[Beta] S+(Tr[\[Sigma][[ElTypId,e,gi]]]/3+\[CapitalKappa] Tr[d\[Epsilon]]) IdentityMatrix[3]
]

Tangent[e0_,dt_,BMat:_,ELEdu:_,ElTypId_,\[Xi]_List]:=
Block[{e=e0,gi,d\[Epsilon],de,S,\[Sigma]equiv,sol\[Epsilon]p,\[CapitalDelta]\[Epsilon]plas,\[Epsilon]plasNew,\[Beta],\[Sigma]new,\[Gamma],factor,\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]},
{\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]}=MaterialProperty;
gi=GaussIndex@\[Xi];
d\[Epsilon]=ConstantArray[0.0,{3,3}];
d\[Epsilon][[;;ndof,;;ndof]]=((BMat[\[Xi]].ELEdu)+Transpose[(BMat[\[Xi]].ELEdu)])/2;
de=(d\[Epsilon]-Tr[d\[Epsilon]]/3 IdentityMatrix[3]);
S =(\[Sigma][[ElTypId,e,gi]]-Tr[\[Sigma][[ElTypId,e,gi]]]/3 IdentityMatrix[3])+\[CapitalEpsilon]/(1+\[Nu]) de;
\[Sigma]equiv=Sqrt[3./2.]Norm[S,"Frobenius"];
ClearAll[x];
sol\[Epsilon]p=NSolve[\[Sigma]equiv/Y-(3\[CapitalEpsilon])/(2 Y (1+\[Nu])) x-(1+(\[Epsilon]plas[[ElTypId,e,gi]]+x)/\[Epsilon]0)^(1./\[ScriptN]) (x/(dt \[Epsilon]dot0 (*Exp[-Q/k T]*)))^(1./\[ScriptM])==0&&x>=0,x,Reals];
\[CapitalDelta]\[Epsilon]plas=x/.sol\[Epsilon]p[[1]];
\[Epsilon]plasNew=\[Epsilon]plas[[ElTypId,e,gi]]+ \[CapitalDelta]\[Epsilon]plas;
\[Beta]=If[\[Sigma]equiv>0,1-(3 \[CapitalEpsilon] \[CapitalDelta]\[Epsilon]plas)/(2(1+\[Nu])\[Sigma]equiv),1.0];
\[Sigma]new=\[Beta] S+(Tr[\[Sigma][[ElTypId,e,gi]]]/3+\[CapitalKappa] Tr[d\[Epsilon]]) IdentityMatrix[3];
S=(\[Sigma]new-Tr[\[Sigma]new]/3 IdentityMatrix[3]);
\[Sigma]equiv=Sqrt[3./2.]Norm[S,"Frobenius"];
If[\[Sigma]equiv*\[CapitalDelta]\[Epsilon]plas>0,\[Beta]=(1+(3 \[CapitalEpsilon] \[CapitalDelta]\[Epsilon]plas)/(2(1+\[Nu])\[Sigma]equiv))^-1;\[Gamma]=\[Beta]((3 \[CapitalEpsilon])/(2(1+\[Nu])\[Sigma]equiv)+(1/(\[ScriptN](\[Epsilon]0+\[Epsilon]plasNew))+1/(\[ScriptM]  \[CapitalDelta]\[Epsilon]plas)));
factor = (9.\[CapitalEpsilon](\[CapitalDelta]\[Epsilon]plas-1/\[Gamma]))/(4.(1+\[Nu])\[Sigma]equiv^3);,\[Beta]=1.;factor = 0.;];
(2 \[Beta] \[Mu](\[DoubleStruckCapitalI]0+factor S\[TensorProduct]S)+\[CapitalKappa] \[ScriptCapitalI])[[;;ndof,;;ndof,;;ndof,;;ndof]]
]


(* ::Input::Initialization:: *)
ClearAll[ComputeResidualMatrixU];
SetAttributes[ComputeResidualMatrixU,HoldFirst];
ComputeResidualMatrixU[rMat_,e0_,UMat_,dt_,ElTypId_]:=
Block[{e=e0,B,Q,jacobi,BMat,ELEf,ELEr,ELEd,\[ScriptCapitalI]r,ELEu,coord},
B=IEN[[ElTypId,;;,e]];
Q=Flatten@IDMat[[;;,B]];
coord=Coords[[B]];
jacobi=Det@((dN@@#).coord)&;
BMat=(Inverse[(dN@@#).coord].dN@@#)&;
ELEu=Transpose[UMat[[;;,B]]];
(*ELEf=-jacobi[#1](3 \[Lambda]+2 \[Mu]) \[Alpha]\[CapitalDelta]T[#2]BMat[#1]&;*)
ELEr=jacobi[#]*stress[e,dt,BMat,ELEu,ElTypId,#][[;;ndof,;;ndof]].BMat[#]&;
ELEd=(*ELEf[#1,#2]*)-ELEr[#1]&;
\[ScriptCapitalI]r= Flatten@GuassIntegrate[coord,ELEd];
rMat[[Q]]+=\[ScriptCapitalI]r;
]


ClearAll[ComputeStiffnessMatrixU];
SetAttributes[ComputeStiffnessMatrixU,HoldFirst];
ComputeStiffnessMatrixU[KMat_,e0_,UMat_,dt_,ElTypId_]:=
Block[{e=e0
,B,Q,jacobi,BMat,ELEk,\[ScriptCapitalI]k,coord,ELEu
},
B=IEN[[ElTypId,;;,e]];
Q=Flatten@IDMat[[;;,B]];
coord=Coords[[B]];
jacobi=Det@((dN@@#).coord)&;
BMat=(Inverse[(dN@@#).coord].dN@@#)&;
ELEu=Transpose[UMat[[;;,B]]];
ELEk=jacobi[#]Transpose[BMat[#]].Tangent[e,dt,BMat,ELEu,ElTypId,#].BMat[#]&;
\[ScriptCapitalI]k=Flatten[GuassIntegrate[coord,ELEk],{{2,1},{3,4}}];
KMat[[Q,Q]]+=\[ScriptCapitalI]k;
]


(* ::Input::Initialization:: *)
ClearAll[UpdateStrainStress];
UpdateStrainStress[\[Sigma]_,\[Epsilon]plas_,dt_,BMat:_,ELEdu:_,\[Xi]_List]:=
Block[{gi,d\[Epsilon],de,S,\[Sigma]equiv,sol\[Epsilon]p,\[CapitalDelta]\[Epsilon]plas,\[Beta],\[Gamma],factor,\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu],d\[Sigma]},
{\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]}=MaterialProperty;
gi=GaussIndex@\[Xi];
d\[Epsilon]=ConstantArray[0.0,{3,3}];
d\[Epsilon][[;;ndof,;;ndof]]=((BMat[\[Xi]].ELEdu)+Transpose[(BMat[\[Xi]].ELEdu)])/2;
de=(d\[Epsilon]-Tr[d\[Epsilon]]/3 IdentityMatrix[3]);
S =(\[Sigma][[gi]]-Tr[\[Sigma][[gi]]]/3 IdentityMatrix[3])+\[CapitalEpsilon]/(1+\[Nu]) de;
\[Sigma]equiv=Sqrt[3./2.]Norm[S,"Frobenius"];
ClearAll[x];
sol\[Epsilon]p=NSolve[\[Sigma]equiv/Y-(3\[CapitalEpsilon])/(2 Y (1+\[Nu])) x-(1+(\[Epsilon]plas[[gi]]+x)/\[Epsilon]0)^(1./\[ScriptN]) (x/(dt \[Epsilon]dot0 (*Exp[-Q/k T]*)))^(1./\[ScriptM])==0&&x>=0,x,Reals];
\[CapitalDelta]\[Epsilon]plas=x/.sol\[Epsilon]p[[1]];
\[Beta]=If[\[Sigma]equiv>0,1-(3 \[CapitalEpsilon] \[CapitalDelta]\[Epsilon]plas)/(2(1+\[Nu])\[Sigma]equiv),1.0];
d\[Sigma]=\[Beta] S+(Tr[\[Sigma][[gi]]]/3+\[CapitalKappa] Tr[d\[Epsilon]]) IdentityMatrix[3]-\[Sigma][[gi]];
{d\[Sigma],\[CapitalDelta]\[Epsilon]plas}
];

ClearAll[UpdateStates];
UpdateStates[\[Sigma]_,\[Epsilon]plas_,e0_,wMat_,dt_,ElTypId_]:=
Block[{e=e0,B,BMat,ELEu,coord},
B=IEN[[ElTypId,;;,e]];
coord=Coords[[B]];
BMat=(Inverse[(dN@@#).coord].dN@@#)&;
ELEu=Transpose[wMat[[;;,B]]];
UpdateStrainStress[\[Sigma],\[Epsilon]plas,dt,BMat,ELEu,#]&/@GuassPointsNatural]



(* ::Input::Initialization:: *)
CalrMat[UMat_,dt_,ElTypId_]:=Block[{GuassPointsNatural,GaussIndex,GuassWeights,NMat,dN,rMat},
DefineGaussAndSFInfo[ElementType[[ElTypId]],integrationOrder,elementOrder];
ParallelEvaluate[rMat=SparseArray[{},{ndof*nnp},0.0]];
ParallelDo[ComputeResidualMatrixU[rMat,n,UMat,dt,ElTypId],{n,Range[nel[[ElTypId]]]}];
rMat=Plus@@(ParallelEvaluate@rMat);
rMat
];
CalKMat[UMat_,dt_,ElTypId_]:= 
Block[{
GuassPointsNatural,GaussIndex,GuassWeights,NMat,dN,KMat
},
DefineGaussAndSFInfo[ElementType[[ElTypId]],integrationOrder,elementOrder];
ParallelEvaluate[KMat=SparseArray[{},{ndof*nnp,ndof*nnp},0.0]];
ParallelDo[ComputeStiffnessMatrixU[KMat,n,UMat,dt,ElTypId],{n,Range[nel[[ElTypId]]]}];
KMat=Plus@@(ParallelEvaluate@KMat);
(*KMat=SparseArray[{},{ndof*nnp,ndof*nnp},0.0];
Do[ComputeStiffnessMatrixU[KMat,n,UMat,dt,ElTypId],{n,Range[nel[[ElTypId]]]}];*)
KMat
]

CalState[\[Sigma]_,\[Epsilon]plas_,wMat_,dt_,ElTypId_]:= 
Block[{GuassPointsNatural,GaussIndex,GuassWeights,NMat,dN,dState,d\[Sigma],d\[Epsilon]plas},
DefineGaussAndSFInfo[ElementType[[ElTypId]],integrationOrder,elementOrder];
dState=(*Parallel*)Map[UpdateStates[\[Sigma][[#]],\[Epsilon]plas[[#]],#,wMat,dt,ElTypId]&,Range[nel[[ElTypId]]]];
d\[Sigma]=dState[[;;,;;,1]];
d\[Epsilon]plas=dState[[;;,;;,2]];
(*Print["dState",dState];
Print["d\[Sigma]",d\[Sigma]];
Print["\[Sigma]",\[Sigma]];
Print["d\[Epsilon]plas",d\[Epsilon]plas];
Print["\[Epsilon]plas",\[Epsilon]plas];*)
{d\[Sigma],d\[Epsilon]plas}
]
ParallelResidual[UMat_,dt_,TracInd_]:= 
Block[{rMat,Err,tMat},
rMat=Plus@@(CalrMat[UMat,dt,#]&/@Range@nElTyp);
If[TracInd,
ParallelEvaluate[tMat=SparseArray[{},{ndof*nnp},0.0]];
ParallelDo[ApplyTraction[tMat,edge],{edge,Edges}];
tMat=Plus@@(ParallelEvaluate@tMat);
rMat+=tMat;
];
(*If[TracInd,ApplyTraction[rMat,#]&/@Edges;];*)
Err =Norm[rMat[[IDno]],Infinity];
{Err,rMat}
]

ParallelStiffness[UMat_,dt_]:= 
Block[{KMat},
KMat=Plus@@(CalKMat[UMat,dt,#]&/@Range@nElTyp);
KMat
]

ParallelUpdateStates[\[Sigma]in_,\[Epsilon]plasin_,wMat_,dt_]:= 
Block[{\[Sigma]=\[Sigma]in,\[Epsilon]plas=\[Epsilon]plasin,dState,d\[Sigma],d\[Epsilon]plas},
dState=CalState[\[Sigma][[#]],\[Epsilon]plas[[#]],wMat,dt,#]&/@Range[nElTyp];
d\[Sigma]=dState[[;;,1]];
d\[Epsilon]plas=dState[[;;,2]];
(*Print["d\[Sigma]",d\[Sigma]];
Print["\[Sigma]",\[Sigma]];
Print["d\[Epsilon]plas",d\[Epsilon]plas];
Print["\[Epsilon]plas",\[Epsilon]plas];*)
\[Sigma]+=d\[Sigma];
\[Epsilon]plas+=d\[Epsilon]plas;
{\[Sigma],\[Epsilon]plas}
]




(* ::Input::Initialization:: *)
ClearAll[ApplyTraction];
SetAttributes[ApplyTraction,HoldFirst];
ApplyTraction[rMat_,Edge_]:=
Block[{
ElementType=Head@mesh["BoundaryElements"][[1]],
elementOrder=mesh["MeshOrder"],
integrationOrder = 2
,OutEdge,coord,jacobi,ELEtMat,ELEt,Q
,GuassPointsNatural,GuassWeights,NMat,dN,NetTrctn
},
GuassPointsNatural=ElementIntegrationPoints[ElementType,integrationOrder];
GuassWeights=ElementIntegrationWeights[ElementType,integrationOrder];
NMat=ElementShapeFunction[ElementType,elementOrder];dN= ElementShapeFunctionDerivative[ElementType,elementOrder];
OutEdge=Flatten[Outer[List,Range[ndof],Edge],1];
coord =Coords[[Edge]];
jacobi =If[ndof==3,Norm[Cross@@((dN@@#).coord)]&
,Norm[(dN@@#).coord]&];
ELEtMat=ArrayReshape[ReplacePart[Map[NeumannBC,OutEdge],Position[KeyExistsQ[NeumannBC,#]&/@OutEdge,False]->0.0],{ndof,nsen}];
ELEt=jacobi[#](ELEtMat.NMat@@#)&;
NetTrctn=GuassWeights.(ELEt/@GuassPointsNatural);
Q=Flatten@IDMat[[;;,Edge]];
rMat[[Q]]+=Flatten[ConstantArray[#/nsen,nsen]&/@NetTrctn];
]


(* ::Input::Initialization:: *)
ClearAll[ComputeStressProjection];
SetAttributes[ComputeStressProjection,HoldFirst];
ComputeStressProjection[{aMat_,UdMat_},e0_,UMat_,\[Sigma]_,ElTypId_]:=
Block[{e=e0,B,jacobi,BMat,\[ScriptCapitalI]k,\[ScriptCapitalI]f,ff,fk,coord,ELEu},
B=IEN[[ElTypId,;;,e]];
coord=Coords[[B]];
jacobi=Det@((dN@@#).coord)&;
BMat=(Inverse[(dN@@#).coord].dN@@#)&;
ELEu=Transpose[UMat[[;;,B]]];
fk=jacobi[#](NMat@@#)\[TensorProduct](NMat@@#)&;
\[ScriptCapitalI]k=GuassIntegrate[coord,fk];
aMat[[B,B]]+=\[ScriptCapitalI]k;
ff=jacobi[#](NMat@@#)\[TensorProduct]Flatten[\[Sigma][[e,GaussIndex@#]]]&;
\[ScriptCapitalI]f=GuassIntegrate[coord,ff];
UdMat[[B,;;]]+=\[ScriptCapitalI]f;
]

CalAUdMat[UMat_,\[Sigma]_,ElTypId_]:= 
Block[{
GuassPointsNatural,GaussIndex,GuassWeights,NMat,dN,aMat,UdMat
},
DefineGaussAndSFInfo[ElementType[[ElTypId]],integrationOrder,elementOrder];
ParallelEvaluate[aMat=SparseArray[{},{nnp,nnp},0.0]];
ParallelEvaluate[UdMat=ConstantArray[0.0,{nnp,9}]];
ParallelDo[ComputeStressProjection[{aMat,UdMat},n,UMat,\[Sigma],ElTypId],{n,Range[nel[[ElTypId]]]}];
aMat=Plus@@(ParallelEvaluate@aMat);
UdMat=Plus@@(ParallelEvaluate@UdMat);
{aMat,UdMat}
]

StressRecover[UMat_,\[Sigma]_]:=Block[{AUdMat,aMat,UdMat,SolUd,SolUdMat,StressMat,StressMatf},
AUdMat=CalAUdMat[UMat,\[Sigma][[#]],#]&/@(Range@nElTyp);
aMat=Plus@@AUdMat[[;;,1]];
UdMat=Plus@@AUdMat[[;;,2]];
SolUd=LinearSolve[aMat,UdMat];
StressMat=ArrayReshape[SolUd,{Length@SolUd,3,3}];
StressMatf=ArrayReshape[ElementMeshInterpolation[{mesh},Flatten[StressMat,{2,3}][[#,;;]]] & /@ Range[9],{3,3}];
StressMatf
]



(* ::Input::Initialization:: *)
(*Only applicable in Linear Elastic*)
(*ComputeRF[UMat_,dt_]:=Block[{KMat,udsol,udMat,RFTotalVec,RFPos},
KMat=ParallelStiffness[];
RFTotalVec=(Flatten[UMat^\[Transpose]][[IDno]].KMat[[IDno,DirichletDof]]+Flatten[UMat^\[Transpose]][[DirichletDof]].KMat[[DirichletDof,DirichletDof]]);
RFPos= Flatten[Position[DirichletDof,#]&/@NeumannDof];
Total@RFTotalVec[[RFPos]]
];*)
ClearAll[CalEE];
CalEE[UMat_,\[Sigma]_,ElTypId_]:=Block[{GuassPointsNatural,GaussIndex,GuassWeights,NMat,dN,Eg},
DefineGaussAndSFInfo[ElementType[[ElTypId]],integrationOrder,elementOrder];
ParallelEvaluate[Eg=0];
ParallelDo[ComputeEE[Eg,n,UMat,\[Sigma],ElTypId],{n,nel[[ElTypId]]}];
Plus@@(ParallelEvaluate@Eg)
]

ClearAll[ComputeEE];
SetAttributes[ComputeEE,HoldFirst];
ComputeEE[Eg_,e0_,UMat_,\[Sigma]_,ElTypId_]:=
Block[{e=e0,B,coord,jacobi,BMat,ELEu,ELE\[Sigma],ELEEg},
B=IEN[[ElTypId,;;,e]];
coord=Coords[[B]];
jacobi=Det@((dN@@#).coord)&;
BMat=(Inverse[(dN@@#).coord].dN@@#)&;
ELEu=Transpose[UMat[[;;,B]]];
ELE\[Sigma]=\[Sigma][[e,GaussIndex@#]][[;;ndof,;;ndof]]&;
ELEEg=jacobi[#]*Tr[ELE\[Sigma][#].(BMat[#].ELEu)]&;
Eg+=GuassIntegrate[coord,ELEEg];
]



(* ::Input::Initialization:: *)
ClearAll[InitializationUState];
SetAttributes[InitializationUState,HoldAll];
InitializationUState[wMat_,uMat_,\[Sigma]_,\[Epsilon]plas:_]:=Block[{},
ngauss=Length/@(ElementIntegrationWeights[#,integrationOrder]&/@ElementType);
wMat=ConstantArray[0.0,{ndof,nnp}];
uMat=ConstantArray[0.0,{ndof,nnp}];
\[Sigma]=MapThread[ConstantArray[0.0,{#1,#2,3,3}]&,{nel,ngauss}];
\[Epsilon]plas=MapThread[ConstantArray[0.0,{#1,#2}]&,{nel,ngauss}];
];
DefineLoadStep[LoadStt_,LoadEnd_,nsteps_,TimePeriod_]:=
Block[
 {dt,StepSize,LoadStep,LoadInc},
dt = TimePeriod/nsteps;
StepSize = (LoadEnd-LoadStt)/nsteps;
LoadStep=Subdivide[LoadStt,LoadEnd,nsteps]/LoadEnd;
LoadInc = LoadStep-Prepend[LoadStep[[;;-2]],0.0];
{dt,LoadStep,LoadInc}//N
]

Inp2Mesh[inp_]:=Block[{MeshString,NodeSttId,ElementTriSttId,ElementQuadSttId,ElementQuadEndId,NodeCoord,ElementTri,ElementQuad},
MeshString =Import[inp,"Data"];
NodeSttId=Position[MeshString,{"*Node"}][[1,1]];
ElementTriSttId=Position[MeshString,{"*Element","type=CPE3"}][[1,1]];
ElementQuadSttId=Position[MeshString,{"*Element","type=CPE4R"}][[1,1]];
ElementQuadEndId=Position[MeshString,"nset=Set-1"][[1,1]];
NodeCoord=MeshString[[NodeSttId+1;;ElementTriSttId-1]];
ElementTri=MeshString[[ElementTriSttId+1;;ElementQuadSttId-1]];
ElementQuad=MeshString[[ElementQuadSttId+1;;ElementQuadEndId-1]];
ToElementMesh["Coordinates"->NodeCoord[[;;,2;;]],"MeshElements"->{TriangleElement[ElementTri[[;;,2;;]]],QuadElement[ElementQuad[[;;,2;;]]]},"MeshOrder"->1]
]


(* ::Input::Initialization:: *)
ClearAll[InitializeFEM];
InitializeFEM[mesh_ElementMesh]:=Block[{
\[CapitalEpsilon]=1000.0,
\[Nu]=0.3,
Y=15.0,
\[Epsilon]0=0.5,
\[ScriptN]=10,
\[ScriptM]=10,
\[Epsilon]dot0=0.1,
\[CapitalKappa],\[Lambda],\[Mu]},
\[CapitalKappa]=\[CapitalEpsilon]/(3(1-2\[Nu]));
\[Lambda]=(\[CapitalEpsilon] \[Nu])/((1+\[Nu])(1-2\[Nu]));
\[Mu]=\[CapitalEpsilon] /(2(1+\[Nu]));
ElementType =Head/@mesh["MeshElements"];
nElTyp=Length@ElementType;
elementOrder=mesh["MeshOrder"];
integrationOrder=2;
Print[mesh];
Coords=mesh["Coordinates"];
IEN=Transpose[Apply[List,mesh["MeshElements"],{1}][[#,1]]]&/@Range[nElTyp];
{nnp,ndof}=Dimensions@Coords;
nen=(Dimensions/@IEN)[[;;,1]];
nel=(Dimensions/@IEN)[[;;,2]];
IENS=Apply[List,mesh["BoundaryElements"],{1}][[1,1]]\[Transpose] ;
{nsen,nsel}=Dimensions@IENS;
\[DoubleStruckCapitalI]0=Table[1/2. (KroneckerDelta[i,r]KroneckerDelta[j,s]+KroneckerDelta[i,s] KroneckerDelta[j,r])-1/3. KroneckerDelta[i,j]KroneckerDelta[r,s],{i,3},{j,3},{r,3},{s,3}];
\[ScriptCapitalI]=IdentityMatrix[3]\[TensorProduct]IdentityMatrix[3];
{\[CapitalEpsilon],\[Nu],Y,\[Epsilon]0,\[ScriptN],\[ScriptM],\[Epsilon]dot0,\[CapitalKappa],\[Lambda],\[Mu]}
];


(* ::Input::Initialization:: *)
ClearAll[NewtonSolve];
NewtonSolve[(*LoadStt_,LoadEnd_,*)nsteps_,TimePeriod_,\[Alpha]_,TracInd_,MaxItr_:50]:=
Block[{tol=10^-5
(*,dt,LoadStep,LoadInc,Load,itr,Err,rMat,KMat,udsol,udMat,Ufvec,
wMat,uMat,\[Sigma],\[Epsilon]plas,DirichletBC,NeumannBC,StressMatflocal
,Fd*)
},
{dt,LoadStep,LoadInc}=DefineLoadStep[0,1,nsteps,TimePeriod];
InitializationUState[wMat,uMat,\[Sigma],\[Epsilon]plas];
Fd=Reap@Do[
itr=0;
Print["Step No. = ",\[ScriptI]];
Print["LoadFactor = ",LoadStep[[\[ScriptI]]]];
DirichletBC=AssociationThread[DirichletPoints->LoadInc[[\[ScriptI]]]DirichletVals];
NeumannBC=AssociationThread[NeumannPoints->LoadStep[[\[ScriptI]]]NeumannVals];
wMat=ReplacePart[wMat, DirichletBC];
{Err,rMat}=ParallelResidual[wMat,dt,TracInd];
While[Err>tol&&itr++<MaxItr,
KMat=ParallelStiffness[wMat,dt];
udsol=LinearSolve[KMat[[IDno,IDno]],rMat[[IDno]]];
udMat=SparseArray[{},{ndof*nnp},0.0];
udMat[[IDno]]=udsol;
wMat+=\[Alpha] Transpose[ArrayReshape[udMat,{nnp,ndof}]];
{Err,rMat}=ParallelResidual[wMat,dt,TracInd];
Print["Iteration: ",itr,". \n Norm of residual for w : ",Err];
];
If[Err<tol,Print["Compute w Converged!"];
{\[Sigma],\[Epsilon]plas}=ParallelUpdateStates[\[Sigma],\[Epsilon]plas,wMat,dt];
uMat+=wMat;
,Print["Compute w Not Converged!"];Break[];];
Sow[wMat,1];
Sow[uMat,2];
Sow[\[Sigma],3];
Sow[\[Epsilon]plas,4];
,{\[ScriptI],nsteps+1}];
{Fd[[2]],dt}
]

PostProcess[wMat_,uMat_,\[Sigma]_,dt_,L_]:=Block[{
Ufvec,StressMatflocal,wfvec,Eg,ExternalWorkf,ExternalWork
},
Ufvec=Table[ElementMeshInterpolation[{mesh}, uMat[[i,;;]]],{i,1,ndof}];
StressMatflocal=StressRecover[uMat,\[Sigma]];
wfvec=Table[ElementMeshInterpolation[{mesh}, wMat[[i,;;]]],{i,1,ndof}];
ExternalWorkf=Through[StressMatflocal[[2,;;2]][#1,#2]].Through[wfvec[#1,#2]]&;
ExternalWork=NIntegrate[ExternalWorkf[x,L],{x,0,L},AccuracyGoal->10];
Eg=Plus@@(CalEE[wMat,\[Sigma][[#]],#]&/@Range@nElTyp);
{Ufvec[[2]]@@{0.5L,L},NIntegrate[StressMatflocal[[2,2]]@@{x,L},{x,0,L},AccuracyGoal->10],Eg,ExternalWork,(ExternalWork-Eg)/dt}
]





