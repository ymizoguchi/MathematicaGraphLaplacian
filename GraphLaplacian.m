(* ::Package:: *)

(* ::Section:: *)
(*GraphLaplacian.m (Mathematica Modules 2012/01/18)*)


(* ::Subsection:: *)
(*Requirements*)


(* ::Text:: *)
(*2010/12/20, 2012/01/18*)


(* ::Text:: *)
(*RandomGraph\:3068EdgeColor\:304c\:8d64\:306b\:306a\:308b. \:65e2\:5b58\:95a2\:6570\:3068\:91cd\:8907\:3057\:3066\:3044\:308b? (2011/01/25)*)


(* ::Text:: *)
(*2012/06/08 Package\:5316 (GraphLaplacian.m) *)
(*2012/11/10 Block Diagonalization (Subsection)*)


BeginPackage["GraphLaplacian`",{"Combinatorica`","ComputationalGeometry`"}];


(* ::Subsection:: *)
(** Fundamental Functions*)


(* \:9802\:70b9 x1 \:3068\:9802\:70b9 x2 \:3068\:306e\:8ddd\:96e2 *)
Distance::Usage="Distance[x1,x2]";
Distance[x1_List,x2_List]:=Sqrt[(x1[[1]]-x2[[1]])^2+(x1[[2]]-x2[[2]])^2];
(* \:30d9\:30af\:30c8\:30eb x \:3068\:30d9\:30af\:30c8\:30eb y \:3068\:306e\:8ddd\:96e2 *)
DistanceVector::Usage="DistanceVector[x_List,y_List]";
DistanceVector[x_List,y_List]:=Sqrt[Total[Map[(#[[1]]-#[[2]])^2&,Transpose[{x,y}]]]];
(* \:5206\:5272\:3057\:305f\:5024\:306e\:30ea\:30b9\:30c8\:3067\:306f\:306a\:304f, \:5206\:5272\:3055\:308c\:305f\:6210\:5206\:756a\:53f7\:306e\:30ea\:30b9\:30c8\:3092\:51fa\:529b\:3059\:308b *)
LabeledFindClusters::Usage="LabeledFindClusters[l,n]";
LabeledFindClusters[l_,n_]:=Module[{size,ev1,ev2},
size=Length[l];
ev1=Transpose[{Table[i,{i,1,size}]}~Join~{l}];
ev2=Map[Rest[#]->First[#]&,ev1];
FindClusters[ev2,n]
];
(* \:6709\:5411\:30b0\:30e9\:30d5\:3092\:7121\:5411\:30b0\:30e9\:30d5\:3078\:5909\:63db\:3059\:308b *)
DirectedToUndirected::Usage="DirectedToUndirected[g]";
DirectedToUndirected[g_]:=Module[{v,e},
FromUnorderedPairs[ToOrderedPairs[g]]
];


(* ::Subsection:: *)
(** Characteristic*)


(* \:9802\:70b9\:306e\:90e8\:5206\:96c6\:5408 s \:3068\:305d\:306e\:88dc\:96c6\:5408 s^c \:306e\:9593\:306b\:3042\:308b\:8fba\:306e\:30ea\:30b9\:30c8 *)
DS[s_,g_]:=Module[{edges,s1,s2},
edges=Edges[g];
s1=Select[Select[edges,MemberQ[s,#[[1]]]&],MemberQ[Complement[Table[i,{i,1,V[g]}],s],#[[2]]]&];
s2=Select[Select[edges,MemberQ[s,#[[2]]]&],MemberQ[Complement[Table[i,{i,1,V[g]}],s],#[[1]]]&];
Join[s1,s2]];
(* \:9802\:70b9\:306e\:90e8\:5206\:96c6\:5408 s \:304b\:3089, \:305d\:306e\:88dc\:96c6\:5408 s^c \:3078\:306e\:6d41\:51fa\:78ba\:7387 *)
FDS[s_,g_]:=Module[{p,m},p=MyStationaryDistribution[g];
m=NaturalRandomWalkMatrix[g];
Total[Map[p[[#[[1]]]]*m[[#[[2]]]][[#[[1]]]]&,DS[s,g]]]];
(* Normalized Cut Value *)
WnCut[s_,g_]:=Module[{sc},sc=Complement[Table[i,{i,1,V[g]}],s];
If[(sc=={})||(s=={}),0,
FDS[s,g]/FS[s,g]+FDS[sc,g]/FS[sc,g]]];
(* \:5168\:3066\:306e\:9802\:70b9\:306e\:90e8\:5206\:96c6\:5408\:306b\:5bfe\:3057\:3066 WnCut\:306e\:5024\:3092\:8a08\:7b97\:3057\:5024\:306e\:5c0f\:3055\:3044\:9806\:756a\:306b\:4e26\:3079\:66ff\:3048\:308b *)
FindMinimumWnCut[g_]:=Module[{s,ss,sl},
ss=Subsets[Table[i,{i,1,V[g]}]];
s= N[Map[WnCut[#,g]&,ss]];
Select[SortBy[Transpose[{s,ss}],#[[1]]&],Not[#[[1]]==0]&]]
(* \:30ea\:30b9\:30c8 l \:306e\:5148\:982d\:304b\:3089\:306e\:90e8\:5206\:30ea\:30b9\:30c8\:306b\:5bfe\:3057\:3066 WnCut\:306e\:5024\:3092\:8a08\:7b97\:3057\:5024\:306e\:5c0f\:3055\:3044\:9806\:756a\:306b\:4e26\:3079\:66ff\:3048\:308b *)
FindMinimumWnCut[g_,l_]:=Module[{s,ss,sl,i},
ss=Table[Ordering[l,i],{i,1,Length[l]}];
s= N[Map[WnCut[#,g]&,ss]];
Select[SortBy[Transpose[{s,ss}],#[[1]]&],Not[#[[1]]==0]&]]


(* \:30b0\:30e9\:30d5 g \:306e\:9802\:70b9 n \:306e\:4f4d\:6570 *)
GDegree[g_,n_]:=InDegree[g,n]+OutDegree[g,n];
(* \:30b0\:30e9\:30d5 g \:306e\:9802\:70b9\:96c6\:5408 s \:306e\:4f4d\:6570 *)
GVol[g_,s_]:=Total[Map[GDegree[g,#]&,s]];
(* \:30b0\:30e9\:30d5 g \:306e\:5168\:9802\:70b9\:4f4d\:6570\:306e\:5408\:8a08 *)
GVol[g_]:=Total[Degrees[g]];
(* \:30b0\:30e9\:30d5 g \:306e HG\:30ab\:30c3\:30c8\:5024 *)
HG[s_,g_]:=Module[{vg,es,s1,s2},vg=Table[i,{i,1,V[g]}];
es=Length[DS[s,g]];
s1=GVol[g,s]; s2=GVol[g,Complement[vg,s]];
If[s1==0,es/s2,If[s2==0,es/s1,es/Min[s1,s2]]]];
FindMinimumHG[g_]:=Module[{s,ss,sl},
ss=Subsets[Table[i,{i,1,V[g]}]];
s= N[Map[HG[#,g]&,ss]];
Select[SortBy[Transpose[{s,ss}],#[[1]]&],Not[#[[1]]==0]&]];
(* \:30b0\:30e9\:30d5 g \:306e Normalized Cut \:5024 *)
Ncut[s_,g_]:=Module[{c,s2,v1,v2},
s2=Complement[Table[i,{i,1,V[g]}],s];
v1=GVol[g,s];v2=GVol[g,s2];c=Length[DS[s,g]];
If[v1==0,c/v2,If[v2==0,c/v1,c(1/v1+1/v2)]]];
(* Note: Subsets \:306f\:30b5\:30a4\:30ba 20\:304f\:3089\:3044\:304c\:9650\:754c!? *)
FindMinimumNcut[g_]:=Module[{s,ss,sl},
ss=Subsets[Table[i,{i,1,V[g]}]];
s= N[Map[Ncut[#,g]&,ss]];
Select[SortBy[Transpose[{s,ss}],#[[1]]&],Not[#[[1]]==0]&]];


(* \:884c\:5217m\:306e\:7b2cn\:884c\:306e\:307f\:3092\:6b8b\:3057\:6b8b\:308a\:30920\:30d9\:30af\:30c8\:30eb\:306b\:3059\:308b *)
TruncateMatrix[m_,n_]:=Module[{l,s1,s2,z},
l=m[[n]];
s1=Length[m[[1]]];
s2=Length[m];
z = Table[0,{s1}];
If[n==1,Prepend[Table[z,{s2-1}],l],If[n==s2,Append[Table[z,{s2-1}],l],Join[Append[Table[z,{n-1}],l],Table[z,{s2-n}]]]]];
(* \:884c\:5217m\:306e\:7b2cn\:884c\:307e\:3067\:3092\:6b8b\:3057\:3066\:6b8b\:308a\:30920\:30d9\:30af\:30c8\:30eb\:306b\:3059\:308b *)
TruncateUptoMatrix[m_,n_]:=Module[{l,s1,s2,z},
l=m[[n]];
s1=Length[m[[1]]];
s2=Length[m];
z = Table[0,{s1}];
If[n==1,Prepend[Table[z,{s2-1}],l],If[n==s2,m,Join[Take[m,n],Table[z,{s2-n}]]]]];


(* \:9802\:70b9\:5217\:3092\:4e09\:89d2\:5f62\:5206\:5272\:3057\:3066, \:305d\:306e\:8fba\:306e\:5217\:3092\:8fd4\:3059 *)
DelaunayEdges[pl_]:=Select[
Flatten[Map[Function[p,Map[{p[[1]],#}&,p[[2]]]],DelaunayTriangulation[pl]],1],#[[1]]<#[[2]]&];
(* \:9802\:70b9\:5217\:3092\:4e0e\:3048\:3066, \:4e09\:89d2\:5f62\:5206\:5272\:3057\:305f\:30b0\:30e9\:30d5\:3092\:8fd4\:3059 *)
DelaunayGraph[pl_]:=CreateGraph[pl,DelaunayEdges[pl]];
(* \:9802\:70b9\:5217 vl \:3068\:8fba\:5217 el \:304b\:3089\:30b0\:30e9\:30d5\:3092\:4f5c\:308b *)
CreateGraph[vl_,el_]:=AddEdges[AddVertices[EmptyGraph[0],vl],el];
(* n\:500b\:306e\:9802\:70b9\:306e\:5ea7\:6a19\:3092\:30e9\:30f3\:30c0\:30e0\:306b\:5f97\:308b. \:5ea7\:6a19\:5024\:306f-1\:304b\:30891\:307e\:3067\:306e\:9593\:3068\:3059\:308b. *)
NVertices[n_]:=RandomReal[{-1,1},{n,2}];
(* \:7121\:5411\:30b0\:30e9\:30d5 g \:306e\:9802\:70b9\:306e\:5ea7\:6a19\:3092 vl \:306b\:3059\:308b *)
SetVertices[g_,vl_]:=CreateGraph[vl,ToUnorderedPairs[g]];
(* \:9802\:70b9\:6570 n, \:8fba\:306e\:5b58\:5728\:78ba\:7387 p \:306e\:9023\:7d50\:30e9\:30f3\:30c0\:30e0\:30b0\:30e9\:30d5\:3092\:4f5c\:6210\:3059\:308b. *)
NRandomGraph[n_,p_]:=Module[{g},
g=SetVertices[RandomGraph[n,p],NVertices[n]];
If[ConnectedQ[g],g,NRandomGraph[n,p]]];
(* n\:9802\:70b9\:306e\:5de1\:56de\:30b0\:30e9\:30d5\:306e\:9802\:70b9\:306e\:5ea7\:6a19\:3092 s \:56de\:8ee2\:3057\:305f\:5ea7\:6a19\:5217 *)
CycleVertices[n_,s_]:=Table[{Cos[k 2\[Pi]/n+s],Sin[k 2\[Pi]/n+s]},{k,1,n}];
(* n\:9802\:70b9\:306e\:5de1\:56de\:30b0\:30e9\:30d5\:306e\:9802\:70b9\:306e\:5ea7\:6a19\:3092 s \:56de\:8ee2\:3057\:305f\:30b0\:30e9\:30d5 *)
CycledGraph[n_,s_]:=SetVertices[Cycle[n],CycleVertices[n,s]];
(* \:5358\:4f4d\:884c\:5217\:306b\:8fd1\:3044\:884c\:5217 a \:306e t\:4e57\:3092\:7d1a\:6570\:5c55\:958b\:3067\:6c42\:3081\:308b *)
NMatrixPower[a_,t_]:=Module[{m,em},
em = IdentityMatrix[Length[a]];
m= a-em;N[em+t m+N[1/2 (-1+t) t ](m.m)+N[1/6 (-2+t) (-1+t) t ](m.m.m)
(*
+N[1/24 (-3+t) (-2+t) (-1+t) t ](m.m.m.m)
+N[1/120 (-4+t) (-3+t) (-2+t) (-1+t) t] (m.m.m.m.m)
+N[1/720 (-5+t) (-4+t) (-3+t) (-2+t) (-1+t) t ](m.m.m.m.m.m)
+N[((-6+t) (-5+t) (-4+t) (-3+t) (-2+t) (-1+t) t )/5040](m.m.m.m.m.m.m)+N[((-7+t) (-6+t) (-5+t) (-4+t) (-3+t) (-2+t) (-1+t) t )/40320](m.m.m.m.m.m.m.m)+N[((-8+t) (-7+t) (-6+t) (-5+t) (-4+t) (-3+t) (-2+t) (-1+t) t)/362880] (m.m.m.m.m.m.m.m.m)+N[((-9+t) (-8+t) (-7+t) (-6+t) (-5+t) (-4+t) (-3+t) (-2+t) (-1+t) t)/3628800] (m.m.m.m.m.m.m.m.m.m)
  *)
]];
(* \:884c\:5217 m \:306e\:5bfe\:89d2\:5316 *)
Diagonalize[m_]:=Module[{p,d},
p=Eigenvectors[m];
d=Chop[p.m.Inverse[p]];
Table[d[[i]][[i]],{i,1,Length[m]}]
];
(* \:8907\:7d20\:6570 c \:306e t\:4e57 *)
ComplexPower[c_,t_]:=Exp[t Log[c]];
(* \:884c\:5217 m \:306e t\:4e57 : \:884c\:5217 m \:306e\:5bfe\:89d2\:5316\:3092\:5229\:7528\:3059\:308b. *)
MatrixT[m_,t_]:=Module[{p,pi,d,dt},
p=N[Eigenvectors[m]];
pi=Inverse[p];
d=Chop[N[p.m.pi]];
dt=Map[ComplexPower[#,t]&,Table[d[[i]][[i]],{i,1,Length[m]}]];
Re[Chop[pi.DiagonalMatrix[dt].p]]];
    (* \:884c\:5217 sm \:306e\:5404\:884c\:30d9\:30af\:30c8\:30eb\:306b\:3064\:3044\:3066 \:884c\:5217 tm \:306e\:884c\:30d9\:30af\:30c8\:30eb\:306e\:3046\:3061\:5185\:7a4d\:6700\:5927\:306e\:7269\:3092\:9078\:3093\:3067 tm \:3092\:4e26\:3079\:66ff\:3048\:308b *)
FindMax[v_,m_,l_]:=Sort[Transpose[{l,Map[v.m[[#]]&,l]}],#[[1]]<#[[2]]&][[1]];
Reordering0[sm_,tm_,l_]:=
If[sm=={},{},Module[{v,mx},
v=First[sm];
mx=FindMax[v,tm,l];
Prepend[Reordering0[Rest[sm],tm,Complement[l,{mx[[1]]}]],tm[[mx[[1]]]]]]];

(* Reordering[sm_,tm_]:=Module[{s,l},
s=Length[sm];
l=Table[i,{i,2,s}];
Prepend[Reordering0[Rest[sm],tm,l],First[sm]]]; *)
Reordering[sm_,tm_]:=tm;
(* \:884c\:5217 sm \:306e\:5404\:5217\:30d9\:30af\:30c8\:30eb\:306b\:3064\:3044\:3066 \:884c\:5217 tm \:306e\:5217\:30d9\:30af\:30c8\:30eb\:306e\:3046\:3061\:5185\:7a4d\:6700\:5927\:306e\:7269\:3092\:9078\:3093\:3067 tm \:3092\:4e26\:3079\:66ff\:3048\:308b *)
TransposeReordering[sm_,tm_]:=Transpose[Reordering[Transpose[sm],Transpose[tm]]];


(* ::Subsection:: *)
(** Show Graphs*)


(* \:30b0\:30e9\:30d5\:8868\:793a\:3059\:308b\:969b\:306e\:9802\:70b9\:306e\:8272\:3065\:3051\:30aa\:30d7\:30b7\:30e7\:30f3\:5f0f\:3092\:4f5c\:308b *)
ColoringVertex0[l_,c_]:=If[l=={},{},{Append[First[l],VertexColor->First[c]]}~Join~ColoringVertex0[Rest[l],Rest[c]]];
(* \:5206\:5272\:7d50\:679c\:3092\:9802\:70b9\:5ea7\:6a19\:306e\:8272\:3065\:3051\:30aa\:30d7\:30b7\:30e7\:30f3\:5f0f\:306b\:5909\:66f4 *)
ColoringVertex[l_]:=ColoringVertex0[l,{Red,Blue,Green,Yellow}];
(* \:30b0\:30e9\:30d5 g \:306e\:9802\:70b9\:306b\:7570\:306a\:308b\:8272\:3092\:3064\:3051\:308b *)
Coloring[g_]:=Module[{cl,s,op},
cl={Red,Green,Blue,Orange,Cyan,Purple,Black};
s=V[g];
op=Transpose[{Table[i,{i,1,s}],Map[VertexColor->#&,Take[cl,s]]}];
SetGraphOptions[g,op]];
(* \:8981\:7d20 n \:304c \:5206\:5272\:30ea\:30b9\:30c8 cl \:306e\:4f55\:756a\:76ee\:306e\:30af\:30e9\:30b9\:306b\:5165\:3063\:3066\:3044\:308b\:304b\:8fd4\:3059\:306e\:304c ClusterNumber[n,cl] *)
(* ClusterNumber[8,{{1,10},{2,5,6,7},{3,4,8},{9}}] = 3 *)
ClusterNumber0[n_,cl_,k_]:=If[cl=={},0,If[MemberQ[First[cl],n],k,ClusterNumber0[n,Rest[cl],k+1]]];
ClusterNumber[n_,cl_]:=ClusterNumber0[n,cl,1];
(* \:30b0\:30e9\:30d5\:306e\:30ea\:30b9\:30c8 gl \:5206\:5272\:30ea\:30b9\:30c8 cl \:306b\:5bfe\:3057\:3066, \:30af\:30e9\:30b9\:30bf\:3054\:3068\:306b\:8272\:5206\:3051\:3057\:3066 ShowGraph \:3059\:308b *)
ShowColoredGraphs[gl_,cl_]:=Module[{colors,nl},
colors={Red,Green,Blue,Orange,Cyan,Purple,Black};
nl=Transpose[{Table[i,{i,1,Length[gl]}],gl}];
Map[ShowGraph[SetGraphOptions[#[[2]],VertexColor->colors[[ClusterNumber[#[[1]],cl]]],EdgeColor->colors[[ClusterNumber[#[[1]],cl]]]]]&,nl]];
(* \:30b0\:30e9\:30d5 g \:306e\:9802\:70b9\:96c6\:5408 a \:3068 a\:306e\:88dc\:96c6\:5408\:306b\:5206\:5272\:3057\:3066\:8272\:3065\:3051\:3059\:308b *)
ColoringSubset[g_,a_]:=SetGraphOptions[g,ColoringVertex[{a,Complement[Table[i,{i,1,V[g]}],a]}]];


(* ::Subsection:: *)
(** Random Walks*)


(* \:30e9\:30f3\:30c0\:30e0\:30a6\:30a9\:30fc\:30af\:306e\:78ba\:7387\:884c\:5217 *)
NaturalRandomWalkMatrix[g_]:=Module[{ga,d},
ga=ToAdjacencyMatrix[g];
d=Transpose[Table[Map[Total[#]&,ga],{Length[ga]}]];
Transpose[ga/d]
];
(* \:30e9\:30f3\:30c0\:30e0\:30a6\:30a9\:30fc\:30af\:306e\:5b9a\:5e38\:5206\:5e03 *)
MyStationaryDistribution[g_]:=Module[{es,e,e2,d},
es=Transpose[Eigensystem[NaturalRandomWalkMatrix[g]]];
e = Select[es,#[[1]]==1&];
e2=If[Length[e]>1,Map[Norm,Transpose[Map[Normalize[#,Total]&,Transpose[e][[2]]]]],e[[1]][[2]]];
(* e=First[Eigenvectors[NaturalRandomWalkMatrix[g]]]; *)
Normalize[e2,Total]
];
(* \:9802\:70b9\:96c6\:5408 s \:306b\:5bfe\:3059\:308b\:5b9a\:5e38\:5206\:5e03\:78ba\:7387\:306e\:7dcf\:548c *)
FS[s_,g_]:=Module[{p},p=MyStationaryDistribution[g];
Total[Map[p[[#]]&,s]]];
(* \:884c\:5217m\:306e\:7b2c1\:56fa\:6709\:30d9\:30af\:30c8\:30eb *)
FirstEigenVector[m_]:=Module[{es,fst,es2},
es=Eigensystem[m];
fst=Sort[es[[1]],#1>#2&][[1]];
es2=Select[Transpose[Eigensystem[m]],#[[1]]==fst&];
If[Length[es2]>1,Transpose[Transpose[es2][[2]]],es2[[1]][[2]]]];


(* ::Subsection:: *)
(** Eigenvalues and Eigenvectors of Matrix*)


(* \:884c\:5217m\:306e\:7b2c2\:56fa\:6709\:30d9\:30af\:30c8\:30eb *)
SecondSmallEigenVector[m_]:=Module[{es,second,es2},
es=N[Eigensystem[m]];
second=Sort[es[[1]],#1<#2&][[2]];
es2=Select[Transpose[es],#[[1]]==second&];
If[Length[es2]>1,Transpose[Transpose[es2][[2]]],es2[[1]][[2]]]];
(* \:884c\:5217m\:306e\:7b2c3\:56fa\:6709\:30d9\:30af\:30c8\:30eb *)
ThirdSmallEigenVector[m_]:=Module[{es,third,es2},
es=N[Eigensystem[m]];
third=Sort[es[[1]],#1<#2&][[3]];
es2=Select[Transpose[es],#[[1]]==third&];
If[Length[es2]>1,Transpose[Transpose[es2][[2]]],es2[[1]][[2]]]];


(* ::Subsection:: *)
(** Adjacency matrix*)


(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:63a5\:7d9a\:95a2\:4fc2\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217 *)
UndirectedLaplacian[g_]:=Module[{ga,d,size},
size=Length[Vertices[g]];
d=DiagonalMatrix[1/Sqrt[Degrees[g]]];
ga=ToAdjacencyMatrix[g];
IdentityMatrix[size]-d.ga.d
];
(* \:9802\:70b9\:306e\:5ea7\:6a19\:5024\:3067\:5206\:5272\:3059\:308b *)
NormalClustering[g_,n_]:=Module[{cl,vs},
vs=Vertices[g];
cl =LabeledFindClusters[vs,n];
SetGraphOptions[g,ColoringVertex[cl]]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306e\:7b2c2\:56fa\:6709\:30d9\:30af\:30c8\:30eb *)
UndirectedSpectralVector[g_]:=Module[{ga,d,d2,size,gb,ev,cl},
size=Length[Vertices[g]];
d=DiagonalMatrix[1/Sqrt[Degrees[g]]];
ga=ToAdjacencyMatrix[g];
gb=IdentityMatrix[size]-d.ga.d;
ev=SecondSmallEigenVector[gb]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306b\:3088\:308b\:30b9\:30da\:30af\:30c8\:30eb\:5206\:5272 (\:7b2c2\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:3092\:4f7f\:3046) (n\:306f\:5206\:5272\:6570) *)
UndirectedSpectralClustering[g_,n_]:=Module[{ev,cl},
ev=UndirectedSpectralVector[g];
cl=LabeledFindClusters[ev,n];
SetGraphOptions[g,ColoringVertex[cl]]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306e\:7b2c2,\:7b2c3\:56fa\:6709\:30d9\:30af\:30c8\:30eb *)
UndirectedSpectralVector2[g_]:=Module[{ga,d,d2,size,gb,ev,cl},
size=Length[Vertices[g]];
d=DiagonalMatrix[1/Sqrt[Degrees[g]]];
ga=ToAdjacencyMatrix[g];
gb=IdentityMatrix[size]-d.ga.d;
ev=Transpose[{SecondSmallEigenVector[gb],ThirdSmallEigenVector[gb]}]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306b\:3088\:308b\:30b9\:30da\:30af\:30c8\:30eb\:5206\:5272 (\:7b2c2,\:7b2c3\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:3092\:4f7f\:3046) *)
UndirectedSpectralClustering2[g_,n_]:=Module[{ev,cl},
ev=UndirectedSpectralVector2[g];
cl=LabeledFindClusters[ev,n];
SetGraphOptions[g,ColoringVertex[cl]]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306b\:3088\:308b\:30b9\:30da\:30af\:30c8\:30eb\:5206\:5272 (\:7b2c2\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:6210\:5206\:3092\:30bd\:30fc\:30c8\:3057\:3066\:4f7f\:3046) *)
UndirectedSpectralClusteringPlus[g_]:=Module[{size,l,cl},
size=Length[Vertices[g]];
l = FindMinimumWnCut[g,UndirectedSpectralVector[g]][[1]][[2]];
cl={l,Complement[Table[i,{i,1,size}],l]};
SetGraphOptions[g,ColoringVertex[cl]]
];
(* \:7121\:5411\:30b0\:30e9\:30d5\:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306b\:3088\:308b\:30b9\:30da\:30af\:30c8\:30eb\:5206\:5272 (\:7b2c2\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:6210\:5206\:306e\:7b26\:53f7\:3092\:4f7f\:3046) *)
UndirectedSpectralClusteringSign[g_]:=Module[{size,sl,l,cl},
size=Length[Vertices[g]];
sl=Table[i,{i,1,size}];
l=Transpose[Select[Transpose[{UndirectedSpectralVector[g],sl}],#1[[1]]<0&]][[2]];
cl={l,Complement[sl,l]};
SetGraphOptions[g,ColoringVertex[cl]]
];
(* \:30d9\:30af\:30c8\:30eb\:5217 m \:3092 PCA\:6cd5\:3092\:7528\:3044\:30663\:3064\:306e\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:306e\:6210\:5206\:3067 n \:500b\:306e\:30af\:30e9\:30b9\:30bf\:306b\:5206\:5272\:3059\:308b *)
PCA3ClusteringData[m_]:=Module[{c,w},
c=m.Transpose[m];
w=Take[Eigenvectors[c],Length[m[[1]]]]//N;
Transpose[w]];
PCA3Clustering[m_,n_]:=LabeledFindClusters[PCA3ClusteringData[m],n];


(* ::Subsection:: *)
(** Block Diagonalization*)


(* Perm1[ev] \:30d9\:30af\:30c8\:30ebev\:306e\:8981\:7d20\:306e\:865a\:90e8\:306e\:5927\:304d\:3044\:9806\:306b\:4e26\:3079\:66ff\:3048\:305f\:969b\:306e\:756a\:53f7\:306e\:30ea\:30b9\:30c8(\:7f6e\:63db)\:3092\:51fa\:529b\:3059\:308b *)
Perm1[ev_]:=Sort[Transpose[{ev,Table[i,{i,1,Length[ev]}]}],Im[#1[[1]]]>Im[#2[[1]]]&];
(* Split1[l] \:884c\:5217l\:306e\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:3092\:56fa\:6709\:5024\:8907\:7d20\:6570\:306b\:5bfe\:3059\:308b\:3082\:306e\:306e\:5bfe\:306e\:30ea\:30b9\:30c8\:3068\:5b9f\:6570\:306b\:5bfe\:5fdc\:3059\:308b\:3082\:306e\:30ea\:30b9\:30c8\:306b\:5206\:3051\:308b *)
Split1s[l_,v_]:=Module[{vp,v0,vm,h,hn},vp=v[[1]];v0=v[[2]];vm=v[[3]];
If[l=={},v,h=Im[First[l][[1]]];hn=First[l][[2]];If[h>0,Split1s[Rest[l],{Append[vp,hn],v0,vm}],If[h==0,Split1s[Rest[l],{vp,Append[v0,hn],vm}],Split1s[Rest[l],{vp,v0,Append[vm,hn]}]]]]];
Split1[l_]:=Module[{vp,v0,vm},{vp,v0,vm}=Split1s[l,{{},{},{}}];{Transpose[{vp,Reverse[vm]}],v0}];
(* Eigenvectors1[m] \:884c\:5217m\:3092\:30d6\:30ed\:30c3\:30af\:5bfe\:89d2\:5316\:3059\:308b\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:306e\:30ea\:30b9\:30c8\:3092\:6c42\:3081\:308b *)
Eigenvectors1[m_]:=Module[{e1,ev1,s1},e1=Orthogonalize[Eigenvectors[m]];ev1=Eigenvalues[m];s1=Split1[Perm1[ev1]];
Join[Flatten[Map[{Normalize[Re[e1[[First[#]]]]],Normalize[Im[e1[[First[#]]]]]}&,First[s1]],1],Map[e1[[#]]&,First[Rest[s1]]]]//Chop];
(* Eigenvalues1[m] \:884c\:5217m\:3092\:30d6\:30ed\:30c3\:30af\:5bfe\:89d2\:5316\:3059\:308b\:56de\:8ee2\:884c\:5217\:306e\:89d2\:5ea6\:306e\:30ea\:30b9\:30c8\:3068\:5b9f\:6570\:56fa\:6709\:5024(1)\:306e\:30ea\:30b9\:30c8\:3092\:6c42\:3081\:308b *)
Eigenvalues1[m_]:=Module[{e1,ev1,s1},e1=Orthogonalize[Eigenvectors[m]];ev1=Eigenvalues[m];s1=Split1[Perm1[ev1]];
{Map[Arg[ev1[[First[#]]]]&,First[s1]],Map[ev1[[#]]&,First[Rest[s1]]]}];
(* EmbedDiagonal[l] \:56de\:8ee2\:89d2\:5ea6\:3068\:5b9f\:6570\:56fa\:6709\:5024\:306e\:30ea\:30b9\:30c8\:304b\:3089\:30d6\:30ed\:30c3\:30af\:5bfe\:89d2\:5316\:884c\:5217\:3092\:6c42\:3081\:308b *)
EmbedDiagonal[l_]:=Module[{r,s,rn,sn,n,a,i,j},r=First[l];s=First[Rest[l]];
rn=Length[r];sn=Length[s];n=2*rn+sn;
a=Table[0,{n},{n}];
For[i=1,i<=rn,i++,
a[[2*(i-1)+1]][[2*(i-1)+1]]=Cos[r[[i]]];a[[2*(i-1)+1]][[2*(i-1)+2]]=Sin[r[[i]]];
a[[2*(i-1)+2]][[2*(i-1)+1]]=-Sin[r[[i]]];a[[2*(i-1)+2]][[2*(i-1)+2]]=Cos[r[[i]]];];
For[i=1,i<=sn,i++,
a[[2*rn+i]][[2*rn+i]]=s[[i]];];
a
];
(* \:56de\:8ee2\:89d2\:5ea6\:3068\:5b9f\:6570\:56fa\:6709\:5024\:306e\:3079\:304d\:4e57 / \:56de\:8ee2\:89d2\:306fx\:500d, \:5b9f\:6570\:56fa\:6709\:5024\:306f\:6b63\:8ca0\:3092\:8003\:616e\:3057\:3066\:3079\:304d\:4e57 *)
RotationPower[l_,x_]:=Module[{r,s},{r,s}=l;
{Map[#*x&,r],Map[If[#>0,1,1-2x]&,s]}];
(* \:30d6\:30ed\:30c3\:30af\:5bfe\:89d2\:5316\:3092\:7528\:3044\:305f\:884c\:5217\:306e\:3079\:304d\:4e57 *)
MatrixPower1[m_,x_]:=Module[{ev1,l},ev1=Eigenvectors1[m];l=Eigenvalues1[m];
Transpose[ev1].EmbedDiagonal[RotationPower[l,x]].ev1//Chop];
(* \:30ea\:30b9\:30c8\:306e\:8981\:7d20n\:3068\:8981\:7d20m\:306e\:4ea4\:63db *)
Swap[l_,n_,m_]:=Table[If[i==n,l[[m]],If[i==m,l[[n]],l[[i]]]],{i,1,Length[l]}];
(* \:30ea\:30b9\:30c8\:306e\:8981\:7d20\:306e\:96c6\:5408n\:306e\:7b26\:53f7\:306e\:53cd\:8ee2 *)
PM[l_,n_]:=Table[If[MemberQ[n,i],-l[[i]],l[[i]]],{i,1,Length[l]}];


(* ::Subsection:: *)
(** Weighted adjacency matrix*)


(* \:30b0\:30e9\:30d5 g \:306e\:6b21\:6570\:3092\:5bfe\:89d2\:884c\:5217\:306b\:3082\:3064\:884c\:5217 *)
GraphDiagonal[g_]:=Module[{ga,ve,s,w,d},
ga=ToAdjacencyMatrix[g];
ve=Vertices[g];
s = V[g];
w=Table[If[Distance[ve[[i]],ve[[j]]]==0,0,1/Distance[ve[[i]],ve[[j]]]],{i,1,s},{j,1,s}];
DiagonalMatrix[Map[Total,w*ga]]];
(* \:30b0\:30e9\:30d5 g \:306e\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217 *)
GraphLaplacianStandard[g_]:=Module[{ga,ve,s,w,d},
ga=ToAdjacencyMatrix[g];
ve=Vertices[g];
s = V[g];
w=Table[If[Distance[ve[[i]],ve[[j]]]==0,0,1/Distance[ve[[i]],ve[[j]]]],{i,1,s},{j,1,s}];
d =DiagonalMatrix[Map[Total,w*ga]];
d-w*ga];
GraphLaplacian[g_]:=Module[{ga,ve,s,w,d},
ga=ToAdjacencyMatrix[g];
ve=Vertices[g];
s = V[g];
w=Table[If[Distance[ve[[i]],ve[[j]]]==0,0,1/Distance[ve[[i]],ve[[j]]]],{i,1,s},{j,1,s}];
d =DiagonalMatrix[Map[1/Sqrt[#]&,Map[Total,w*ga]]];
IdentityMatrix[s]-d.w.d];
(* \:30b0\:30e9\:30d5\:306e\:56fa\:6709\:5024\:3092\:6c42\:3081\:308b *)
GraphEigenvalues[g_]:=Chop[Sort[Eigenvalues[N[GraphLaplacian[g]]]]];
(* \:30b0\:30e9\:30d5\:306e\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:3092\:6c42\:3081\:308b *)
GraphEigenvectors[g_]:=Chop[Transpose[Sort[Transpose[Eigensystem[N[GraphLaplacian[g]]]],#1[[1]]<#2[[1]]&]][[2]]];
(* \:9802\:70b9\:306e\:5ea7\:6a19\:3092\:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306e\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:3067\:8868\:73fe\:3057\:305f\:5ea7\:6a19 *)
AB[g_]:=Chop[Orthogonalize[GraphEigenvectors[g]].Vertices[g]];
(* \:30e9\:30d7\:30e9\:30b7\:30a2\:30f3\:884c\:5217\:306e\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:306b\:3088\:308b\:76f4\:4ea4\:884c\:5217 *)
R[g_]:=Transpose[Chop[Orthogonalize[GraphEigenvectors[g]]]];


(* ::Subsection:: *)
(** Interpolation*)


(* \:6975\:5ea7\:6a19\:5909\:63db *)
Polar[a_]:=Module[{x,y,r,s},x=a[[1]];y=a[[2]];r=Sqrt[x*x+y*y];s=If[x==0,If[y>=0,\[Pi]/2,-( \[Pi]/2)],ArcTan[x,y]];{r,s}];
(* \:30c7\:30ab\:30eb\:30c8\:5ea7\:6a19\:5909\:63db *)
Cartesian[a_]:=Module[{x,y,r,s},r=a[[1]];s=a[[2]];x=r Cos[s];y=r Sin[s];{x,y}];
(* \:7dda\:5f62\:88dc\:9593 \:59cb\:70b9 a \:7d42\:70b9 b \:30d1\:30e9\:30e1\:30fc\:30bf t=0->1 *)
LinearInterpolate[a_,b_,t_]:=a+t(b-a);
(* \:6975\:5ea7\:6a19\:88dc\:9593 \:59cb\:70b9 a \:7d42\:70b9 b \:30d1\:30e9\:30e1\:30fc\:30bf t=0->1 *)
PolarInterpolate[a_,b_,t_]:=Module[{pa,pb},
	pa=Polar[a];pb=Polar[b];
	If[pa[[2]]-pb[[2]]>\[Pi],pb[[2]]=pb[[2]]+2\[Pi],If[pb[[2]]-pa[[2]]>\[Pi],pb[[2]]=pb[[2]]-2\[Pi]]];
	Cartesian[LinearInterpolate[pa,pb,t]]];
(* \:70b9\:5217 pl \:3092 p \:3060\:3051\:5e73\:884c\:79fb\:52d5\:3059\:308b *)
pt[p_,pl_]:=Map[p+#&,pl];
(* \:70b9\:5217 pl \:306e\:91cd\:5fc3\:70b9\:3092\:6c42\:3081\:308b *)
Cog[pl_]:={Mean[Map[#[[1]]&,pl]],Mean[Map[#[[2]]&,pl]]};
(* \:70b9\:5217 pl \:306e\:91cd\:5fc3\:304b\:3089\:306e\:76f8\:5bfe\:5ea7\:6a19\:3092\:6c42\:3081\:308b *)
CogTrans[pl_]:=pt[-Cog[pl],pl];
(* \:5408\:6210\:88dc\:9593: \:91cd\:5fc3\:306f\:7dda\:5f62\:88dc\:9593. \:76f8\:5bfe\:5ea7\:6a19\:306f\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:5909\:63db\:3092\:5229\:7528 *)
CompositeInterpolate[a_,ac_,b_,bc_,t_]:=
Module[{pa,pb},pa=Polar[a-ac];pb=Polar[b-bc];
If[pa[[2]]-pb[[2]]>\[Pi],pb[[2]]=pb[[2]]+2\[Pi],If[pb[[2]]-pa[[2]]>\[Pi],pb[[2]]=pb[[2]]-2\[Pi]]];
LinearInterpolate[ac,bc,t]+Cartesian[LinearInterpolate[pa,pb,t]]];
(* \:958b\:59cb\:30b0\:30e9\:30d5 sg, \:7d42\:4e86\:30b0\:30e9\:30d5 tg \:306e\:9802\:70b9\:5ea7\:6a19\:306e\:7dda\:5f62\:88dc\:9593 0<=t<= 1 *)
AB[sg_,tg_,t_]:=Module[{SS,TT},
SS=Transpose[R[sg]];
TT=Transpose[R[tg]];
(* TT=Reordering[SS,Transpose[R[tg]]]; *)
Map[LinearInterpolate[#[[1]],#[[2]],t]&,Transpose[{Chop[SS.Vertices[sg]],Chop[TT.Vertices[tg]]}]] 
];
(* \:958b\:59cb\:30b0\:30e9\:30d5 sg, \:7d42\:4e86\:30b0\:30e9\:30d5 tg \:306e\:9802\:70b9\:5ea7\:6a19\:306e\:6975\:5ea7\:6a19\:88dc\:9593 0<=t<= 1 *)
ABPolar[sg_,tg_,t_]:=Module[{SS,TT},
SS=Transpose[R[sg]];
TT=Transpose[R[tg]]; 
(* TT=Reordering[SS,Transpose[R[tg]]];*)
Map[PolarInterpolate[#[[1]],#[[2]],t]&,Transpose[{Chop[SS.Vertices[sg]],Chop[TT.Vertices[tg]]}]]];
(* \:30b9\:30da\:30af\:30c8\:30e9\:30eb\:5909\:63db\:306e\:5909\:63db\:884c\:5217\:306e\:88dc\:9593 0<=t<=1 *)
MM[sg_,tg_,t_]:=Module[{RR,TT,SS},
SS=R[sg];
TT=R[tg];
(* TT=TransposeReordering[SS,R[tg]]; *)
RR=Chop[TT.Inverse[SS]];
(* N[NMatrixPower[RR,t].SS] *)
(* N[MatrixT[RR,t].SS] *)
N[MatrixPower1[RR,t].SS]
];
(* \:5408\:6210\:88dc\:9593: \:91cd\:5fc3\:306f\:7dda\:5f62\:88dc\:9593. \:76f8\:5bfe\:5ea7\:6a19\:306f\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:5909\:63db\:3092\:5229\:7528 *)
SpectralInterpolate[sg_,tg_,t_]:=
Module[{pa,pb,pab,a,b,ac,bc,ag,bg},a=Vertices[sg];b=Vertices[tg];
ac=Cog[a];bc=Cog[b];
ag=SetVertices[sg,Map[N[#-ac]&,a]];bg=SetVertices[tg,Map[N[#-bc]&,b]];
Map[LinearInterpolate[ac,bc,t]+#&,MM[ag,bg,t].AB[ag,bg,t]]
];
(* \:5408\:6210\:88dc\:9593: \:91cd\:5fc3\:306f\:7dda\:5f62\:88dc\:9593. \:76f8\:5bfe\:5ea7\:6a19\:306f\:56fa\:6709\:30d9\:30af\:30c8\:30eb\:5909\:63db\:3092\:5229\:7528 *)
SpectralPolarInterpolate[sg_,tg_,t_]:=
Module[{pa,pb,pab,a,b,ac,bc,ag,bg},a=Vertices[sg];b=Vertices[tg];
ac=Cog[a];bc=Cog[b];
pa=Map[N[Polar[#-ac]]&,a];pb=Map[N[Polar[#-bc]]&,b];
pab=Transpose[Map[
If[#[[1]][[2]]-#[[2]][[2]]>\[Pi],{#[[1]],N[{#[[2]][[1]],#[[2]][[2]]+2\[Pi]}]},If[#[[1]][[2]]-#[[2]][[2]]>\[Pi],{#[[1]],N[{#[[2]][[1]],#[[2]][[2]]-2\[Pi]}]},#],#]&,Transpose[{pa,pb}]]];
ag=SetVertices[sg,Map[N[#-ac]&,a]];bg=SetVertices[tg,Map[N[#-bc]&,b]];
Map[LinearInterpolate[ac,bc,t]+#&,MM[ag,bg,t].ABPolar[ag,bg,t]]
];


(* ::Subsection:: *)
(** Roach Graph*)


(* \:3072\:3052\:306e\:9802\:70b9\:304c n \:500b, \:306f\:3057\:3054\:306e\:9802\:70b9\:304c k \:500b\:306eRoach\:30b0\:30e9\:30d5 *)
RoachEdges[n_,k_]:=Join[Table[{i,i+1},{i,1,n+k-1}],Table[{i,i+1},{i,n+k+1,2(n+k)-1}],Table[{i,i+n+k},{i,n+1,n+k}]];
RoachVertices[n_,k_]:=Join[Table[{i*10,10},{i,1,n+k}],Table[{(i-n-k)*10,-10},{i,n+k+1,2(n+k)}]];
RoachGraph[n_,k_]:=CreateGraph[RoachVertices[n,k],RoachEdges[n,k]];
(* \:9802\:70b9\:306b\:91cd\:307f\:306e\:3042\:308b\:96a3\:63a5\:884c\:5217\:306b\:5bfe\:3059\:308b Normalized Laplacian *)
WeightedNormalizedLaplacian[m_]:=Module[{size,d},
size=Length[m];
d=DiagonalMatrix[1/Sqrt[Map[Total,m]]];
IdentityMatrix[size]-d.m.d
];
(* \:9802\:70b9\:6570 n+k \:306e Path\:30b0\:30e9\:30d5\:3067, k \:500b\:306e\:9802\:70b9\:306b\:91cd\:307f 1 \:304c\:3064\:3044\:305f\:30b0\:30e9\:30d5 *)
WeightedPath[n_,k_]:=Module[{d},
d=Join[Table[0,{n}],Table[1,{k}]];
DiagonalMatrix[d]+ToAdjacencyMatrix[Path[n+k]]
];
(* \:9802\:70b9\:6570 n \:306e Path\:30b0\:30e9\:30d5\:3068, \:9802\:70b9\:6570 k \:306ePath\:30b0\:30e9\:30d5\:3067\:9802\:70b9\:306b\:91cd\:307f 1 \:304c\:3042\:308b\:30b0\:30e9\:30d5\:306e\:548c\:30b0\:30e9\:30d5 *)
WeightedPathUnion[n_,k_]:=Module[{d},
d=Join[Table[0,{n}],Table[1,{k}]];
DiagonalMatrix[d]+ToAdjacencyMatrix[GraphUnion[Path[n],Path[k]]]
];
(* 6k\:9802\:70b9\:306eroach graph\:306e\:8fba\:3092\:8a08\:7b97\:3059\:308b *)
RoachEdges[k_]:= (* Join[Table[{i,i+1},{i,1,3*k-1}],Table[{3*k+i,3*k+i+1},{i,1,3*k-1}],Table[{2*k+i,5*k+i},{i,1,k}]] *)
RoachEdges[2*k,k];
(* 6k\:9802\:70b9\:306eroach graph\:3092\:4f5c\:6210\:3059\:308b *)
RoachGraph[k_]:=(* AddEdges[EmptyGraph[6k],RoachEdges[k]] *)
RoachGraph[2*k, k];


(* ::Subsection:: *)
(** Lollipop Graph*)


(* ::Text:: *)
(* (Subscript[LP, n, m] = LPG[n, m], Subscript[(LP'), n, m] = LPG2[n, m])*)


LPG0[n_,m_]:=Join[Table[{2+m-k,0},{k,1,m}],Table[N[{Cos[(2\[Pi] k)/n],Sin[(2\[Pi] k)/n]}],{k,0,n-1}]];
LPGE0[n_,m_]:=Join[Flatten[Table[{m+i,m+j},{i,1,n},{j,i+1,n}],1],{{m,m+1}},Table[{i,i+1},{i,1,m-1}]];
LPG[n_,m_]:=CreateGraph[LPG0[n,m],LPGE0[n,m]];
LPG2[n_,m_]:=CreateGraph[LPG0[n,m],Append[LPGE0[n,m],{1,m+2}]];


(* ::Subsection:: *)
(** Double Tree Graph*)


(* ::Text:: *)
(* (Subscript[DT, n] = DT2[n] )*)


(* \:6728: \:30b5\:30a4\:30ba n \:5217 k (1,...,n) \:306e\:6700\:521d\:306e\:9802\:70b9\:756a\:53f7 *)
DTK[n_,k_]:=2^n-2^(n-k+1)+1;
(* \:6728: \:30b5\:30a4\:30ba n \:5217 k (1,...,n) \:306e\:9802\:70b9\:6570 *)
DTKS[n_,k_]:=2^(n-k);
(* \:6728: \:30b5\:30a4\:30ba n \:306e\:9802\:70b9 *)
DT[n_]:=Table[Table[DTK[n,k]+i-1,{i,1,DTKS[n,k]}],{k,1,n}];
(* \:6728: \:30b5\:30a4\:30ba n \:306e\:9802\:70b9\:6570 *)
DTS[n_]:=2^n-1;
(* \:6728: \:30b5\:30a4\:30ba n \:5217 k (1,...,n) \:306e\:6700\:521d\:306e\:9802\:70b9\:5ea7\:6a19 *)
DTKSX[n_,k_]:=Table[{k-1,2^k (i-1)+2^(k-1)-1},{i,1,DTKS[n,k]}];
(* \:6728: \:30b5\:30a4\:30ba n \:306e\:9802\:70b9\:5ea7\:6a19 *)
DTX[n_]:=Flatten[Table[DTKSX[n,k],{k,1,n}],1];
(* \:4e8c\:91cd\:6728: DTX1\:53cd\:5bfe\:5074\:306e\:9802\:70b9\:5ea7\:6a19, DTX2\:4e8c\:91cd\:6728\:5168\:4f53\:306e\:9802\:70b9\:5ea7\:6a19 *)
DTX1[n_]:=Map[{2n-1-#[[1]],2(2^(n-1)-1)-#[[2]]}&,Reverse[DTX[n]]];
DTX2[n_]:=Join[DTX[n],DTX1[n]];
(* \:6728: \:30b5\:30a4\:30ba n \:5217 k \:3068\:5217 k-1 \:306e\:9593\:306e\:8fba *)
DTEK[n_,k_]:=Flatten[Table[{{DTK[n,k-1]+2 (i-1),DTK[n,k]+i-1},{DTK[n,k-1]+2 (i-1)+1,DTK[n,k]+i-1}},{i,1,DTKS[n,k]}],1];
(* \:6728: \:30b5\:30a4\:30ba n \:306e\:8fba *)
DTE[n_]:=Flatten[Table[DTEK[n,k],{k,2,n}],1];
(* \:4e8c\:91cd\:6728: DTE1\:53cd\:5bfe\:5074\:306e\:8fba, DTE2\:4e8c\:91cd\:6728\:5168\:4f53\:306e\:8fba *)
DTE1[n_]:=Map[Function[{x},Map[2*DTS[n]-#+1&,x]],DTE[n]];
DTE2[n_]:=Join[DTE[n],DTE1[n],{{DTS[n],DTS[n]+1}}];
(* \:6728: \:30b5\:30a4\:30ba n \:306e\:30b0\:30e9\:30d5 *)
DTG[n_]:=CreateGraph[DTX[n],DTE[n]];
(* \:4e8c\:91cd\:6728: \:30b5\:30a4\:30ba n \:306e\:30b0\:30e9\:30d5 *)
DTG2[n_]:=CreateGraph[DTX2[n],DTE2[n]];


(* ::Subsection:: *)
(** Dobule Tree Cross Path*)


(* ::Text:: *)
(* (Subscript[DT, n] Subscript[xP, m]=DTCPG2[n,m])*)
(*2012/02/03*)


(* \:6728x\:9053\:306e\:9802\:70b9\:6570 *)
DTCPS[n_,m_]:=m DTS[n];
(* \:6728x\:9053\:306e\:9802\:70b9\:5ea7\:6a19 *)
DTCPX[n_,m_]:=Flatten[Table[
Map[{#[[1]]+i n,#[[2]]+i}&,DTX[n]],{i,0,m-1}],1];
(* \:4e8c\:91cd\:6728x\:9053\:306e\:9802\:70b9\:5ea7\:6a19 *)
DTCPX2[n_,m_]:=Flatten[Table[
Map[{#[[1]]+2 i n,#[[2]]+i}&,DTX2[n]],{i,0,m-1}],1];
(* \:6728*\:9053\:306e\:8fba *)
DTCPE[n_,m_]:=Module[{dts,e,p},
dts=DTS[n];
e=Flatten[Table[Map[{#[[1]]+i dts,#[[2]]+i dts}&,DTE[n]],{i,0,m-1}],1];
p=Flatten[Table[Table[{i+k dts,i+(k+1)dts},{i,1, dts}],{k,0,m-2}],1];
Join[e,p]];
(* \:4e8c\:91cd\:6728*\:9053\:306e\:8fba e: \:4e8c\:91cd\:6728\:5185\:306e\:8fba, p: \:4e8c\:91cd\:6728\:9593\:306e\:8fba *)
DTCPE2[n_,m_]:=Module[{dts,e,p},
dts=2 DTS[n];
e=Flatten[Table[Map[{#[[1]]+i dts,#[[2]]+i dts}&,DTE2[n]],{i,0,m-1}],1];
p=Flatten[Table[Table[{i+k dts,i+(k+1)dts},{i,1, dts}],{k,0,m-2}],1];
Join[e,p]];
(* \:30b5\:30a4\:30ba n \:5217\:306e\:6728\:3068\:9577\:3055 m \:306e\:9053\:306e\:7a4d\:30b0\:30e9\:30d5 *)
DTCPG[n_,m_]:=CreateGraph[DTCPX[n,m],DTCPE[n,m]];
(* \:30b5\:30a4\:30ba n \:5217\:306e\:4e8c\:91cd\:6728\:3068\:9577\:3055 m \:306e\:9053\:306e\:7a4d\:30b0\:30e9\:30d5 *)
DTCPG2[n_,m_]:=CreateGraph[DTCPX2[n,m],DTCPE2[n,m]];


EndPackage[];
