import Mathlib

/-!
# Kings in Tournament Graphs

We use Mathlib's 'Digraph V' to represent directed graphs
Vertices represent teams, and 'G.adj v u' means that v defeated u

Our main goal is to prove that every vertex of maximum outdegree
in a finite tournament is a king.

We also proved that a finite, nonempty tournament where every
vertex loses at least once has at least three distinct kings.
-/

namespace TournamentKings

/-! ## Tournament Assumptions

We use Mathlib's directed graphs.
Asymmetry prvents edges in both directs and rules out self-loops.
Trichotomy ensures that distinct vertices have an edge between them.
-/

variable {V : Type*}

noncomputable section

/-! ## Counting Outgoing Neighbors

For finite V, the expression

  Finset.univ.filter (G.Adj v)

contains exactly the vertices that v points to.
Its cardinality

  (Finset.univ.filter (G.Adj v)).card

is the outdegree of v.

We use these Mathlib expressions directly rather than introduce
seperate wrappers for the set and its cardinality.
-/

/-! ## Kings

A king reaches every other vertex in one or two directed steps.
We define this property using Mathlib's adjacency relation.
-/

/-- A vertex that reaches every other vertex in one or two steps -/
def IsKing (G : Digraph V) (v : V) : Prop :=
  ∀ u, u ≠ v →
    G.Adj v u ∨ ∃ w, G.Adj v w ∧ G.Adj w u

/-! ## Maximum Outdegree

In theorem statements, we express maximality directly:


  ∀ u, (Finset.univ.filter (G.Adj u)).card ≤
    (Finset.univ.filter (G.Adj v)).card

This says that every vertex u has at most as many outgoing
neighbors as v. Ties are allowed.
-/

/-! ## Finite-Set Reasoning

Mathlib's memebership lemmas let simp translate membership in
Finset.univ.filter (G.Adj v) into the proposition G.Adj v u

Classical decidability allows these filter to appear directly
in subsequent theorem statements as well as proofs
-/

open scoped Classical

/-! ## Existence of a Maximum-Outdegree Vertex

Every finite, nonempty directed graph has a vertex with
maximum outdegree. No tournament assumptions are needed.
We apply Mathlib's theorem that a function on a nonempty
finite set attains a maximum.
-/

/-- A finite, nonempty digraph has a maximum-outdegree vertex. -/
theorem exists_maximum_outdegree [Fintype V] [Nonempty V]
    (G : Digraph V) :
    ∃ v, ∀ u,
      (Finset.univ.filter (G.Adj u)).card ≤
        (Finset.univ.filter (G.Adj v)).card := by
  obtain ⟨v, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V)
      (fun v : V => (Finset.univ.filter (G.Adj v)).card)
      Finset.univ_nonempty
  exact ⟨v, fun u => hmax u (Finset.mem_univ u)⟩

/-! ## Unreachable Vertices

If v cannot reach a distinct vertex u in one or two steps,
then u points to v and every outgoing neighbor of v.

Trichotomy provides the possible directions between vertices.
Asymmetry and finiteness are not needed for this lemma.
-/

/-- An unreachable vertex points to v and all its outgoing neighbors. -/
theorem unreachable_beats_all
    (G : Digraph V) [Std.Trichotomous G.Adj] (v u : V)
    (hne : u ≠ v)
    (hno_direct : ¬ G.Adj v u)
    (hno_two : ¬ ∃ w, G.Adj v w ∧ G.Adj w u) :
    G.Adj u v ∧ ∀ w, G.Adj v w → G.Adj u w := by
  constructor
  · -- Trichotomy and the assumptions force u → v.
    rcases trichotomous_of G.Adj u v with huv | heq | hvu <;> aesop
  · intro w hvw
    -- The other cases contradict the absence of a direct or two-step route.
    rcases trichotomous_of G.Adj u w with huw | heq | hwu <;> aesop

/-! ## Comparing Outdegrees

If u points to v and every outgoing neighbor of v,
then u has strictly more outgoing neighbors than v.
We prove this using strict inclusion of finite sets.
-/

/-- Points to v and all its outgoing neighbors gives u greater outdegree. -/
theorem outdegree_lt_of_beats_all
    [Fintype V] (G : Digraph V) [Std.Asymm G.Adj]
    (v u : V)
    (huv : G.Adj u v)
    (hall : ∀ w, G.Adj v w → G.Adj u w) :
    (Finset.univ.filter (G.Adj v)).card <
      (Finset.univ.filter (G.Adj u)).card := by
  apply Finset.card_lt_card
  constructor
  · -- Every outgoing neighbor of v is an outgoing neighbor of u.
    intro w hw
  -- The innter simpa turns membership into adjacency
  -- The outer simpa turns adjacency back into membership
    simpa using hall w (by simpa using hw)
  · -- Reverse inclusion would force v to point to itself.
    intro hreverse
    have hmem : v ∈ Finset.univ.filter (G.Adj u) := by
      simpa using huv
    have hvv : G.Adj v v := by
      simpa using hreverse hmem
    exact Std.Asymm.asymm v v hvv hvv


/-! ## Main Theorem

Every maximum-outdegree vertex in a finite tournament is a king.
An unreachable vertex would have greater outdegree,
contradicting maximality.
-/

/-- Every maximum-outdegree vertex in a finite tournament is a king. -/
theorem maximum_outdegree_isKing
    [Fintype V] (G : Digraph V)
    [Std.Asymm G.Adj] [Std.Trichotomous G.Adj]
    (v : V)
    (hmax : ∀ u,
      (Finset.univ.filter (G.Adj u)).card ≤
        (Finset.univ.filter (G.Adj v)).card) :
    IsKing G v := by
  intro u hne
  by_cases hvu : G.Adj v u
  · exact Or.inl hvu
  · right
    by_contra hno_two
    -- An unreachable vertex points to v and all its outgoing neighbors.
    obtain ⟨huv, hall⟩ :=
      unreachable_beats_all G v u hne hvu hno_two
    -- Such a vertex has greater outdegree, contradicting maximality.
    exact (not_lt_of_ge (hmax u))
      (outdegree_lt_of_beats_all G v u huv hall)

/-! ## Existence of a King

A finite, nonempty tournament has a maximum-outdegree vertex.
The main theorem shows that this vertex is a king.
-/

/-- Every finite, nonempty tournament has a king. -/
theorem exists_king
    [Finite V] [Nonempty V] (G : Digraph V)
    [Std.Asymm G.Adj] [Std.Trichotomous G.Adj] :
    ∃ v, IsKing G v := by
  -- Supply an enumeration for the finite-set counting arguments.
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨v, hmax⟩ := exists_maximum_outdegree G
  exact ⟨v, maximum_outdegree_isKing G v hmax⟩

/-! ## Finding a King Among Incoming Neighbors

If some vertex points to v, then a king points to v.
Choose a vertex of maximum outdegree among those pointing to v.
If it were not a king, an unreachable vertex would also point
to v and have greater outdegree, contradicting the choice.
-/

/-- Every vertex with an incoming neighbor has an incoming king. -/
theorem exists_king_adj
    [Finite V] (G : Digraph V)
    [Std.Asymm G.Adj] [Std.Trichotomous G.Adj]
    (v : V) (hin : ∃ u, G.Adj u v) :
    ∃ k, IsKing G k ∧ G.Adj k v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  -- Collect the vertices pointing to v.
  let S : Finset V := Finset.univ.filter (fun u => G.Adj u v)
  obtain ⟨u, huv⟩ := hin
  have hS : S.Nonempty := ⟨u, by simpa [S] using huv⟩
  -- Maximize the full outdegree among vertices in S.
  obtain ⟨k, hk, hmax⟩ :=
  -- All candidates are restricted to S, but their wins are counted over V
    Finset.exists_max_image S
      (fun k : V => (Finset.univ.filter (G.Adj k)).card) hS
  have hkv : G.Adj k v := by
    simpa [S] using hk
  refine ⟨k, ?_, hkv⟩
  -- Choose k as the witness
  -- It already points to v, only IsKing remains.
  intro w hne
  by_cases hkw : G.Adj k w
  · exact Or.inl hkw
  · right
    by_contra hno_two
    obtain ⟨hwk, hall⟩ :=
      unreachable_beats_all G k w hne hkw hno_two
    -- The unreachable vertex also points to v, so belongs to S.
    have hwS : w ∈ S := by
      simpa [S] using hall v hkv
    -- Maximlaity applies only within S, so we need hwS before comparing degrees
    exact (not_lt_of_ge (hmax w hwS))
      (outdegree_lt_of_beats_all G k w hwk hall)

/-! ## At Least Three Kings

If every vertex has an incoming neighbor, then a finite,
nonempty tournament has at least three distinct kings.

Start with a king a. Find a king b pointing to a,
then a king c pointing to b. Asymmetry forces all three
vertices to be distinct.
-/

/-- A finite, nonempty tournament where every vertex loses
    at least once has at least three distinct kings. -/
theorem exists_three_kings
    [Finite V] [Nonempty V] (G : Digraph V)
    [Std.Asymm G.Adj] [Std.Trichotomous G.Adj]
    (hin : ∀ v, ∃ u, G.Adj u v) :
    ∃ a b c,
      IsKing G a ∧ IsKing G b ∧ IsKing G c ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a, ha⟩ := exists_king G
  obtain ⟨b, hb, hba⟩ := exists_king_adj G a (hin a)
  obtain ⟨c, hc, hcb⟩ := exists_king_adj G b (hin b)
-- Identifying a with b would make b → a a self-loop.
  have hab : a ≠ b := by
    intro heq
    subst b
    exact Std.Asymm.asymm a a hba hba
  -- Identifying a with c would give both b → a and a → b.
  have hac : a ≠ c := by
    intro heq
    subst c
    exact Std.Asymm.asymm b a hba hcb
  -- Identifying b with c would make c → b a self-loop.
  have hbc : b ≠ c := by
    intro heq
    subst c
    exact Std.Asymm.asymm b b hcb hcb
  exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩

end
end TournamentKings
