% Generated from psi.p schema for syj207 benchmarking
% N = 1, m = 2

fof(axiom1,axiom,(
( ( p1 <=> p2)  => ( p1 & ( p2 ) ) ) )).
fof(axiom2,axiom,(
( ( p2 <=> p1)  => ( p1 & ( p2 ) ) ) )).

fof(con,conjecture,(
( p0 | ( p1 & ( p2 ) ) | ~(p0 ) )
)).


