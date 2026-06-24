% Generated from chi.p schema for syj201 benchmarking
% N = 2, m = 5

fof(axiom1,axiom,(
( ( p1 <=> p2)  => ( (p1 & (p2 & (p3 & (p4 & p5)))) ) ) )).

fof(axiom2,axiom,(
( ( p2 <=> p3)  => ( (p1 & (p2 & (p3 & (p4 & p5)))) ) ) )).

fof(axiom3,axiom,(
( ( p3 <=> p4)  => ( (p1 & (p2 & (p3 & (p4 & p5)))) ) ) )).

fof(axiom4,axiom,(
( ( p4 <=> p5)  => ( (p1 & (p2 & (p3 & (p4 & p5)))) ) ) )).

fof(axiom5,axiom,(
( ( p5 <=> p1)  => ( (p1 & (p2 & (p3 & (p4 & p5)))) ) ) )).

fof(con,conjecture,(
( (p1 & (p2 & (p3 & (p4 & p5)))) )
)).
