# TournamentKings

Material was ported over from [this repo](https://github.com/kieranr-13/tournament-kings) on 18 Nov.

This project formalizes results about kings in finite tournament graphs in Lean 4 using Mathlib's Digraph structure. A king is a vertex that can reach every other vertex in at most two directed steps.

I proved that every maximum-outdegree vertex is a king, so every finite, nonempty tournament has a king. I also proved that if every vertex has an incoming neighbor, then the tournament has at least three distinct kings.

I chose this project because it resembled a sports tournament and I thought it would be interest to prove a result that relates to sports.  
