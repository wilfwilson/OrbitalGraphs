#
gap> START_TEST("OrbitalGraphs package: orbitalgraphs.tst");
gap> LoadPackage("orbitalgraphs", false);;

# Issue 19
gap> graphs := OrbitalGraphs(Group([(3,4), (5,6)]));;
gap> Length(graphs);
14
gap> ForAll(graphs, D -> DigraphVertices(D) = [1 .. 6]);
true
gap> List(graphs, DigraphNrEdges);
[ 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4 ]
gap> ForAny(graphs, D -> IsDigraphEdge(D, [5, 3]));
true
gap> ForAny(graphs, D -> IsDigraphEdge(D, [3, 5]));
true

# S50product: disjoint S50 x C2 x C2 x S50 x C2 x C2 x D8 on [3 .. 114]
gap> S50product := Group(
> [ ( 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,
>      27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,
>      51,52), (3,4), (53,54), (55,56),
>   ( 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
>       75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92,
>      93, 94, 95, 96, 97, 98, 99,100,101,102,103,104,105,106), (57,58),
>   (107,108), (109,110), (111,112,113,114), (112,114) ] );
<permutation group with 10 generators>
gap> orbitals := OrbitalGraphs(S50product);;
gap> ForAll(orbitals, D -> IsDigraph(D) and DigraphNrVertices(D) = 114);
true
gap> List(orbitals, DigraphNrEdges);
[ 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 50, 
  50, 50, 50, 50, 50, 50, 50, 100, 100, 100, 100, 100, 100, 100, 100, 100, 
  100, 100, 100, 100, 100, 100, 100, 200, 200, 200, 200, 2450, 2450, 2500, 
  2500 ]
gap> PositionsProperty(orbitals, IsSymmetricDigraph);
[ 13, 16, 19, 22, 39, 48, 77, 78 ]
gap> List(orbitals, x -> DigraphEdges(x)[1]);
[ [ 1, 2 ], [ 2, 1 ], [ 1, 53 ], [ 1, 55 ], [ 1, 107 ], [ 1, 109 ], 
  [ 2, 53 ], [ 2, 55 ], [ 2, 107 ], [ 2, 109 ], [ 53, 1 ], [ 53, 2 ], 
  [ 53, 54 ], [ 55, 1 ], [ 55, 2 ], [ 55, 56 ], [ 107, 1 ], [ 107, 2 ], 
  [ 107, 108 ], [ 109, 1 ], [ 109, 2 ], [ 109, 110 ], [ 1, 111 ], [ 2, 111 ], 
  [ 53, 55 ], [ 53, 107 ], [ 53, 109 ], [ 55, 53 ], [ 55, 107 ], [ 55, 109 ], 
  [ 107, 53 ], [ 107, 55 ], [ 107, 109 ], [ 109, 53 ], [ 109, 55 ], 
  [ 109, 107 ], [ 111, 1 ], [ 111, 2 ], [ 111, 113 ], [ 53, 111 ], 
  [ 55, 111 ], [ 107, 111 ], [ 109, 111 ], [ 111, 53 ], [ 111, 55 ], 
  [ 111, 107 ], [ 111, 109 ], [ 111, 112 ], [ 1, 3 ], [ 1, 57 ], [ 2, 3 ], 
  [ 2, 57 ], [ 3, 1 ], [ 3, 2 ], [ 57, 1 ], [ 57, 2 ], [ 3, 53 ], [ 3, 55 ], 
  [ 3, 107 ], [ 3, 109 ], [ 53, 3 ], [ 53, 57 ], [ 55, 3 ], [ 55, 57 ], 
  [ 57, 53 ], [ 57, 55 ], [ 57, 107 ], [ 57, 109 ], [ 107, 3 ], [ 107, 57 ], 
  [ 109, 3 ], [ 109, 57 ], [ 3, 111 ], [ 57, 111 ], [ 111, 3 ], [ 111, 57 ], 
  [ 3, 4 ], [ 57, 58 ], [ 3, 57 ], [ 57, 3 ] ]

#
gap> STOP_TEST("OrbitalGraphs package: orbitalgraphs.tst", 0);