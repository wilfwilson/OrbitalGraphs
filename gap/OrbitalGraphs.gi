#
# OrbitalGraphs: Computations with orbital graphs
#
# Implementations
#

# The code below was originally essentially stolen from ferret.
# Do we want to give different versions of this:
#   a naive version that just computes all orbital graphs,
#   a version that only gives a representative in the isomorphism class, and
#   a version that gives the ones actually used in backtrack?
#
InstallMethod(OrbitalGraphs, "for a permutation group", [IsPermGroup],
function(G)
    local orb, orbitsG, iorb, graph, graphlist, val, p, i, innerorblist,
          orbreps, fillRepElts, maxval;

  # TODO: Option?
  maxval := LargestMovedPoint(G);

  fillRepElts := function(G, orb)
    local val, g, reps, buildorb, gens;
    reps := [];
    reps[orb[1]] := ();
    buildorb := [orb[1]];
    gens := GeneratorsOfGroup(G);
    for val in buildorb do
      for g in gens do
        if not IsBound(reps[val^g]) then
          reps[val^g] := reps[val] * g;
          Add(buildorb, val^g);
        fi;
      od;
    od;
    return reps;
  end;

  graphlist := [];
  orbitsG := Orbits(G, [1..maxval]);
  innerorblist := List(orbitsG, o -> Orbits(Stabilizer(G, o[1]), [1..LargestMovedPoint(G)]));

  for i in [1..Length(orbitsG)] do
    orb := orbitsG[i];
    orbreps := [];

    for iorb in innerorblist[i] do
      if orb[1] <> iorb[1] then
        graph := List([1..LargestMovedPoint(G)], x -> []);
        if IsEmpty(orbreps) then
          orbreps := fillRepElts(G, orb);
        fi;
        for val in orb do
          p := orbreps[val];
          graph[val] := List(iorb, x -> x ^ p);
        od;
        AddSet(graphlist, Digraph(graph));
      fi;
    od;
  od;
  return graphlist;
end);

InstallMethod(OrbitalClosure, "for a permutation group", [IsPermGroup],
G -> Intersection(List(OrbitalGraphs(G), AutomorphismGroup)));
# TODO: TwoClosure as implemented by Heiko Theißen requires the group
#       to be transitive.
# H := TwoClosure(G);

InstallMethod(OrbitalIndex, "for a permutation group", [IsPermGroup],
{G} -> Index(OrbitalClosure(G), G));

InstallMethod(IsOrbitalGraphRecognisable, "for a permutation group",
[IsPermGroup],
# It holds that G <= OrbitalClosure(G), hence testing for size is sufficient
{G} -> Size(OrbitalClosure(G)) = Size(G));

InstallMethod(IsStronglyOrbitalGraphRecognisable, "for a permutation group",
[IsPermGroup],
# TODO check that this is right
{G} -> ForAny(OrbitalGraphs(G), x -> Size(G) = Size(AutomorphismGroup(x))));

InstallMethod(IsAbsolutelyOrbitalGraphRecognisable, "for a permutation group",
[IsPermGroup],
# TODO check that this is right.
{G} -> ForAll(OrbitalGraphs(G), x -> Size(G) = Size(AutomorphismGroup(x))));

InstallTrueMethod(IsStronglyOrbitalGraphRecognisable,
                  IsAbsolutelyOrbitalGraphRecognisable);
InstallTrueMethod(IsOrbitalGraphRecognisable,
                  IsStronglyOrbitalGraphRecognisable);

# Transformation Semigroups

InstallMethod(OrbitalGraphs, "for a transformation semigroup",
[IsTransformationSemigroup],
function(S)
    # FIXME This is currently super-naive
    local bpts;

    bpts := Arrangements([1..LargestMovedPoint(S)], 2);
    return List(bpts, x -> DigraphByEdges(AsList(Enumerate(Orb(S, x, OnTuples)))));
end);
