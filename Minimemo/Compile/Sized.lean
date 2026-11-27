/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Compile
public import Minimemo.Program.Sized

/-!
# The program of a model is sized

This file proves that the translation of a model writes a sized program.

Fix a size for every choice. A scope is well formed if each of its choices has the size of its
domain, each of its links joins two choices of the same size, and the scopes inside it are well
formed. The translation of an expression or a statement, from a well formed scope and where the
sizes of the choices that it makes are the sizes of their domains, writes sized terms and steps
and leaves a well formed scope.

## Main definitions

* `Memo.Scope.WF dom size S`: the scope `S` is well formed.
* `Memo.Agrees size n l`: the choices with the numbers from `n` have the sizes in the list `l`.

## Main results

* `Memo.Expr.sized_term`, `Memo.Stmt.sized_steps`: the translation writes sized terms and steps.
* `Memo.Model.sized_program`: the program of a model is sized, with the sizes of the model.
* `Memo.Model.sized_tables`: every table that the program of a model computes is sized.
-/

@[expose] public section

universe u

namespace Memo

variable {A N D K : Type u} [DecidableEq A] [DecidableEq N] [DecidableEq D]
  (dom : D → Domain K) (size : ℕ → ℕ)

/-- The choices with the numbers from `n` have the sizes in the list `l`. -/
def Agrees (n : ℕ) (l : List ℕ) : Prop := ∀ j (h : j < l.length), size (n + j) = l[j]

variable {size}

theorem agrees_append {n : ℕ} {a b : List ℕ} :
    Agrees size n (a ++ b) ↔ Agrees size n a ∧ Agrees size (n + a.length) b := by
  constructor
  · intro h
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · have := h j (by rw [List.length_append]; omega)
      rwa [List.getElem_append_left hj] at this
    · have := h (a.length + j) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨ha, hb⟩ j hj
    rw [List.length_append] at hj
    by_cases hja : j < a.length
    · rw [List.getElem_append_left hja]
      exact ha j hja
    · rw [List.getElem_append_right (by omega), ← hb (j - a.length) (by omega)]
      congr 1
      omega

theorem agrees_cons {n x : ℕ} {l : List ℕ} :
    Agrees size n (x :: l) ↔ size n = x ∧ Agrees size (n + 1) l := by
  rw [show x :: l = [x] ++ l from rfl, agrees_append]
  refine and_congr ⟨fun h ↦ by simpa using h 0 (by simp), fun h j hj ↦ ?_⟩ Iff.rfl
  obtain rfl : j = 0 := by simpa using hj
  simpa using h

theorem agrees_flatMap_mid {α : Type*} (f : α → List ℕ) {n : ℕ} {l a b : List α} {x : α}
    (hl : l = a ++ x :: b) (h : Agrees size n (l.flatMap f)) :
    Agrees size (n + (a.flatMap f).length) (f x) := by
  subst hl
  rw [List.flatMap_append, List.flatMap_cons, agrees_append, agrees_append] at h
  exact h.2.1

theorem finRange_split {k : ℕ} (i : Fin k) :
    List.finRange k = (List.finRange k).take i ++ i :: (List.finRange k).drop (i + 1) := by
  have h : (i : ℕ) < (List.finRange k).length := by simp
  calc List.finRange k = (List.finRange k).take i ++ (List.finRange k).drop i :=
        (List.take_append_drop _ _).symm
    _ = (List.finRange k).take i ++ (List.finRange k)[(i : ℕ)] :: (List.finRange k).drop (i + 1) := by
        rw [List.getElem_cons_drop]
    _ = _ := by simp

theorem mem_of_lookup {α β : Type*} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    rw [List.lookup_cons] at h
    split at h
    · rename_i heq
      obtain rfl : p.2 = b := by simpa using h
      obtain rfl : a = p.1 := eq_of_beq heq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem allSome_eq_some {k : ℕ} {β : Type*} {o : Fin k → Option β} {b : Fin k → β} :
    allSome o = some b ↔ ∀ i, o i = some (b i) := by
  unfold allSome
  split_ifs with h
  · simp only [Option.some.injEq, funext_iff]
    exact forall_congr' fun i ↦
      ⟨fun hb ↦ hb ▸ (Option.some_get _).symm, fun hb ↦ by simp [hb]⟩
  · refine iff_of_false (by simp) fun hb ↦ h fun i ↦ ?_
    simp [hb i]

theorem sized_foldr_after (l : List (Step K)) (t : Term K) (hl : ∀ s ∈ l, s.sized size = true)
    (ht : t.sized size = true) : (l.foldr Term.after t).sized size = true := by
  induction l with
  | nil => exact ht
  | cons s l ih =>
    simp only [List.foldr_cons, Term.sized, Bool.and_eq_true]
    exact ⟨hl s List.mem_cons_self, ih fun s' h ↦ hl s' (List.mem_cons_of_mem _ h)⟩

variable (size)

/-- A scope is **well formed** if each of its choices has the size of its domain, each of its links
joins two choices of the same size, and the scopes inside it are well formed. -/
inductive Scope.WF : Scope A N D → Prop
  | mk {S : Scope A N D} (entries : ∀ p ∈ S.entries, size p.2.index = (dom p.2.dom).size)
      (links : ∀ l ∈ S.links, size l.1 = size l.2)
      (agents : ∀ α Sα, S.agents α = some Sα → Scope.WF Sα) : Scope.WF S

variable {dom size} {S : Scope A N D}

namespace Scope.WF

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem entries' : Scope.WF dom size S → ∀ p ∈ S.entries, size p.2.index = (dom p.2.dom).size
  | ⟨h, _, _⟩ => h

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem links' : Scope.WF dom size S → ∀ l ∈ S.links, size l.1 = size l.2
  | ⟨_, h, _⟩ => h

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem agents' : Scope.WF dom size S → ∀ α Sα, S.agents α = some Sα → Scope.WF dom size Sα
  | ⟨_, _, h⟩ => h

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem agent (h : Scope.WF dom size S) (α : A) : Scope.WF dom size (S.agent α) := by
  unfold Scope.agent
  cases hα : S.agents α with
  | none => exact ⟨by simp, by simp, by simp⟩
  | some Sα => exact h.agents' α Sα hα

omit [DecidableEq N] [DecidableEq D] in
theorem setAgent (h : Scope.WF dom size S) {Sα : Scope A N D} (hα : Scope.WF dom size Sα)
    (α : A) : Scope.WF dom size (S.setAgent α Sα) := by
  refine ⟨h.entries', h.links', fun β Sβ hβ ↦ ?_⟩
  simp only [Scope.setAgent, Function.update_apply] at hβ
  split_ifs at hβ
  · obtain rfl : Sα = Sβ := by simpa using hβ
    exact hα
  · exact h.agents' β Sβ hβ

omit [DecidableEq D] in
theorem insert (h : Scope.WF dom size S) (a : Ref A × N) {e : Entry D}
    (he : size e.index = (dom e.dom).size) : Scope.WF dom size (S.insert a e) := by
  refine ⟨fun p hp ↦ ?_, h.links', h.agents'⟩
  rcases List.mem_cons.1 hp with rfl | hp
  · exact he
  · exact h.entries' p (List.mem_of_mem_filter hp)

omit [DecidableEq D] in
theorem erase (h : Scope.WF dom size S) (as : List (Ref A × N)) :
    Scope.WF dom size (S.erase as) :=
  ⟨fun p hp ↦ h.entries' p (List.mem_of_mem_filter hp), h.links', h.agents'⟩

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem table (h : Scope.WF dom size S) (w : ℕ) : Scope.WF dom size { S with table := w } :=
  ⟨h.entries', h.links', h.agents'⟩

omit [DecidableEq D] in
theorem lookup (h : Scope.WF dom size S) {a : Ref A × N} {c : Entry D}
    (hc : S.entries.lookup a = some c) : size c.index = (dom c.dom).size :=
  h.entries' (a, c) (mem_of_lookup hc)

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem uncertain (h : Scope.WF dom size S) : sizedVars size (S.uncertain dom) = true := by
  rw [sizedVars_iff]
  intro v hv
  obtain ⟨p, hp, hv⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hv)
  split_ifs at hv
  obtain rfl : (p.2.index, (dom p.2.dom).size) = v := by simpa using hv
  exact (h.entries' p hp).symm

end Scope.WF

omit [DecidableEq D] in
theorem Scope.WF.foldl_insert (mk : N → Ref A × N) (c : Bool) (n : ℕ) :
    ∀ (xs : List (N × D)) (k : ℕ) (S : Scope A N D),
      Agrees size (n + k) (xs.map fun p ↦ (dom p.2).size) → Scope.WF dom size S →
      Scope.WF dom size ((xs.zipIdx k).foldl
        (fun S p ↦ S.insert (mk p.1.1) ⟨n + p.2, p.1.2, c, false⟩) S)
  | [], _, _, _, hS => hS
  | x :: xs, k, S, ha, hS => by
    rw [List.map_cons, agrees_cons] at ha
    rw [List.zipIdx_cons, List.foldl_cons]
    exact Scope.WF.foldl_insert mk c n xs (k + 1) _ ha.2 (hS.insert _ ha.1)

omit [DecidableEq N] [DecidableEq D] in
theorem sizedVars_zipIdx (n : ℕ) : ∀ (xs : List (N × D)) (k : ℕ),
    Agrees size (n + k) (xs.map fun p ↦ (dom p.2).size) →
      ∀ v ∈ (xs.zipIdx k).map (fun p ↦ (n + p.2, (dom p.1.2).size)), v.2 = size v.1
  | [], _, _, v, hv => by simp at hv
  | x :: xs, k, ha, v, hv => by
    rw [List.map_cons, agrees_cons] at ha
    rw [List.zipIdx_cons, List.map_cons] at hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ha.1.symm
    · exact sizedVars_zipIdx n xs (k + 1) ha.2 v hv

omit [DecidableEq D] in
theorem Scope.WF.foldl_copy (β : A) : ∀ (l : List ((Ref A × N) × Entry D)) (S : Scope A N D),
    (∀ p ∈ l, size p.2.index = (dom p.2.dom).size) → Scope.WF dom size S →
    Scope.WF dom size (l.foldl (fun S p ↦
      if p.1.1 = .self then S.insert (.agent β, p.1.2) { p.2 with given := true } else S) S)
  | [], _, _, hS => hS
  | p :: l, S, hl, hS => by
    rw [List.foldl_cons]
    refine Scope.WF.foldl_copy β l _ (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)) ?_
    split_ifs
    · exact hS.insert _ (hl p List.mem_cons_self)
    · exact hS

theorem sized_push_step {g : Gen K} (hg : ∀ st ∈ g.steps, st.sized size = true) {s : Step K}
    (hs : s.sized size = true) : ∀ st ∈ g.steps.push s, st.sized size = true := fun st hst ↦ by
  rcases Array.mem_push.1 hst with h | rfl
  · exact hg st h
  · exact hs

mutual

/-- The translation of an expression writes a sized term. -/
theorem Expr.sized_term : ∀ (e : Expr A N D K) (S : Scope A N D) (g : Gen K) (t : Term K)
    (deps : List ℕ), Expr.term dom e S g = some (t, deps) → Scope.WF dom size S →
    Agrees size g.next (Expr.sizes dom e) → (∀ st ∈ g.steps, st.sized size = true) →
    t.sized size = true
  | .lit r, S, g, t, deps, h, _, _, _ => by
    rw [Expr.term] at h
    obtain ⟨rfl, -⟩ : Term.lit r = t ∧ [] = deps := by simpa using h
    rfl
  | .op f es, S, g, t, deps, h, hS, ha, hg => by
    rw [Expr.term] at h
    obtain ⟨ts, hts, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    rw [allSome_eq_some] at hts
    rw [Expr.sizes] at ha
    simp only [Term.sized, List.all_eq_true]
    intro i _
    exact Expr.sized_term (es i) S _ (ts i).1 (ts i).2 (hts i) hS
      (agrees_flatMap_mid _ (finRange_split i) ha) hg
  | .choice x, S, g, t, deps, h, hS, _, _ => by
    rw [Expr.term] at h
    obtain ⟨c, hc, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    simp only [Term.sized, beq_iff_eq]
    exact (hS.lookup hc).symm
  | .query α e, S, g, t, deps, h, hS, ha, hg => by
    rw [Expr.term] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨Sα, hα, ⟨t', deps'⟩, he, h⟩ := h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rw [Expr.sizes] at ha
    simp only [Term.sized, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    exact ⟨(hS.agents' α Sα hα).links',
      Expr.sized_term e Sα g t' deps' he (hS.agents' α Sα hα) ha hg⟩
  | .expect e, S, g, t, deps, h, hS, ha, hg => by
    rw [Expr.term] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨t', deps'⟩, he, h⟩ := h
    rw [Expr.sizes] at ha
    have ht' := Expr.sized_term e S g t' deps' he hS ha hg
    dsimp only at h
    split_ifs at h
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ht'
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [Term.sized, Bool.and_eq_true]
      exact ⟨hS.uncertain, ht'⟩
  | .imagine s e, S, g, t, deps, h, hS, ha, hg => by
    rw [Expr.term] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨S', g'⟩, hs, ⟨t', deps'⟩, he, h⟩ := h
    rw [Expr.sizes, agrees_append] at ha
    obtain ⟨hS', hg', hn⟩ := Stmt.sized_steps s S g S' g' hs hS ha.1 hg
    have ht' := Expr.sized_term e S' g' t' deps' he hS' (hn ▸ ha.2) hg'
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact sized_foldr_after _ _
      (fun st hst ↦ hg' st (Array.mem_def.2 (List.mem_of_mem_drop hst))) ht'

/-- The translation of a statement, from a well formed scope, writes sized steps and leaves a well
formed scope, and it makes as many choices as the statement has sizes. -/
theorem Stmt.sized_steps : ∀ (s : Stmt A N D K) (S : Scope A N D) (g : Gen K)
    (S' : Scope A N D) (g' : Gen K), Stmt.steps dom s S g = some (S', g') →
    Scope.WF dom size S → Agrees size g.next (Stmt.sizes dom s) →
    (∀ st ∈ g.steps, st.sized size = true) →
    Scope.WF dom size S' ∧ (∀ st ∈ g'.steps, st.sized size = true) ∧
      g'.next = g.next + (Stmt.sizes dom s).length
  | .pass, S, g, S', g', h, hS, _, hg => by
    rw [Stmt.steps] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨hS, hg, by simp [Stmt.sizes]⟩
  | .seq s₁ s₂, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨S₁, g₁⟩, h₁, h₂⟩ := h
    rw [Stmt.sizes, agrees_append] at ha
    obtain ⟨hS₁, hg₁, hn₁⟩ := Stmt.sized_steps s₁ S g S₁ g₁ h₁ hS ha.1 hg
    obtain ⟨hS₂, hg₂, hn₂⟩ := Stmt.sized_steps s₂ S₁ g₁ S' g' h₂ hS₁ (hn₁ ▸ ha.2) hg₁
    exact ⟨hS₂, hg₂, by rw [hn₂, hn₁, Stmt.sizes, List.length_append, Nat.add_assoc]⟩
  | .thinks α s, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨Sα, g₁⟩, h₁, h₂⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
    rw [Stmt.sizes] at ha
    obtain ⟨hSα, hg₁, hn₁⟩ := Stmt.sized_steps s (S.agent α) g Sα g₁ h₁ (hS.agent α) ha hg
    exact ⟨hS.setAgent hSα α, hg₁, by rw [hn₁, Stmt.sizes]⟩
  | .chooses α x X e, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨⟨t, deps⟩, he, h⟩ := h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [Stmt.sizes, agrees_cons] at ha
    have hSα := (hS.agent α).insert (.self, x) (e := ⟨g.next, X, true, false⟩) ha.1
    have ht := Expr.sized_term e _ _ t deps he hSα ha.2 hg
    refine ⟨((hS.insert _ ha.1).setAgent hSα α).table _, sized_push_step hg ?_, ?_⟩
    · simp only [Step.sized, Term.sized, sizedVars, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      exact ⟨ha.1.symm, hSα.links', ht⟩
    · simp only [Stmt.sizes, List.length_cons]
      omega
  | .choosesMax α x X e, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨⟨t, deps⟩, he, h⟩ := h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [Stmt.sizes, agrees_cons] at ha
    have hSα := (hS.agent α).insert (.self, x) (e := ⟨g.next, X, true, false⟩) ha.1
    have ht := Expr.sized_term e _ _ t deps he hSα ha.2 hg
    refine ⟨((hS.insert _ ha.1).setAgent hSα α).table _, sized_push_step hg ?_, ?_⟩
    · simp only [Step.sized, Term.sized, sizedVars, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      exact ⟨ha.1.symm, hSα.links', ha.1.symm, ht⟩
    · simp only [Stmt.sizes, List.length_cons]
      omega
  | .choosesMany α xs e, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨⟨t, deps⟩, he, h⟩ := h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [Stmt.sizes, agrees_append, List.length_map] at ha
    have hSα := Scope.WF.foldl_insert (fun x ↦ (Ref.self, x)) true g.next xs 0 _ ha.1 (hS.agent α)
    have ht := Expr.sized_term e _ _ t deps he hSα ha.2 hg
    refine ⟨((Scope.WF.foldl_insert (fun x ↦ (Ref.agent α, x)) false g.next xs 0 _ ha.1
      hS).setAgent hSα α).table _, sized_push_step hg ?_, ?_⟩
    · simp only [Step.sized, Term.sized, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
      exact ⟨sizedVars_iff.2 (sizedVars_zipIdx g.next xs 0 ha.1), hSα.links', ht⟩
    · simp [Stmt.sizes, Nat.add_assoc]
  | .observes α β x γ y, S, g, S', g', h, hS, _, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨Sα, hα, c, hc, cα, hcα, _, _, h⟩ := h
    split_ifs at h with hcond
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hSα := hS.agents' α Sα hα
    have hsz : size cα.index = (dom cα.dom).size := hSα.lookup hcα
    have hSα' : Scope.WF dom size
        { Sα.insert (.agent β, x) { cα with certain := true, given := true } with
          links := (cα.index, c.index) :: Sα.links } :=
      ⟨(hSα.insert (.agent β, x) (e := { cα with certain := true, given := true }) hsz).entries',
        fun l hl ↦ by
          rcases List.mem_cons.1 hl with rfl | hl
          · rw [hsz, hS.lookup hc, hcond.1]
          · exact hSα.links' l hl,
        hSα.agents'⟩
    exact ⟨hS.setAgent (hSα'.table _) α, sized_push_step hg hSα'.uncertain, by simp [Stmt.sizes]⟩
  | .observesEvent α e, S, g, S', g', h, hS, ha, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨⟨t, deps⟩, he, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [Stmt.sizes] at ha
    have ht := Expr.sized_term e _ _ t deps he (hS.agent α) ha hg
    refine ⟨hS.setAgent ((hS.agent α).table _) α, ?_, by simp [Stmt.sizes]⟩
    exact sized_push_step (g := ⟨g.next, g.steps.push _⟩)
      (sized_push_step hg (by simpa [Step.sized] using ht)) (hS.agent α).uncertain
  | .knows α γ y, S, g, S', g', h, hS, _, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    have hsz := hS.lookup hc
    cases γ with
    | self =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨(hS.insert (.agent α, y) hsz).setAgent ((hS.agent α).insert (.self, y)
        (e := { c with certain := true, given := true }) hsz) α, hg, by simp [Stmt.sizes]⟩
    | agent β =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨hS.setAgent (((hS.agent α).insert (.agent β, y)
        (e := { c with certain := true, given := true }) hsz).setAgent
        (((hS.agent α).agent β).insert (.self, y)
          (e := { c with certain := true, given := true }) hsz) β) α, hg, by simp [Stmt.sizes]⟩
  | .snapshot α β, S, g, S', g', h, hS, _, hg => by
    rw [Stmt.steps] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hSα := hS.agent α
    have hSβ : Scope.WF dom size
        { S.agent α with
          entries := (S.agent α).entries.map fun p ↦ (p.1, { p.2 with given := true })
          links := [] } :=
      ⟨fun p hp ↦ by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          exact hSα.entries' q hq,
        by simp, hSα.agents'⟩
    exact ⟨hS.setAgent ((Scope.WF.foldl_copy β _ _ hSα.entries' hSα).setAgent hSβ β) α, hg,
      by simp [Stmt.sizes]⟩
  | .forgets α xs, S, g, S', g', h, hS, _, hg => by
    rw [Stmt.steps] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Gen.push] at h
    obtain ⟨Sα, hα, h⟩ := h
    split_ifs at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨((hS.erase _).setAgent ((hS.agents' α Sα hα).erase _) α).table _,
      sized_push_step hg ?_, by simp [Stmt.sizes]⟩
    simp only [Step.sized]
    rw [sizedVars_iff]
    intro v hv
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hv)
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact (hS.lookup hc).symm

end

theorem agrees_getD (l : List ℕ) : Agrees (fun i ↦ l.getD i 0) 0 l := fun j hj ↦ by
  simp [List.getD_eq_getElem?_getD, hj]

omit [DecidableEq A] [DecidableEq N] [DecidableEq D] in
theorem wf_axes : ∀ (xs : List (N × D)) (k : ℕ),
    Agrees size k (xs.map fun p ↦ (dom p.2).size) →
      ∀ q ∈ (xs.zipIdx k).map
          (fun p ↦ (((Ref.self, p.1.1) : Ref A × N), (⟨p.2, p.1.2, true, false⟩ : Entry D))),
        size q.2.index = (dom q.2.dom).size
  | [], _, _, q, hq => by simp at hq
  | x :: xs, k, ha, q, hq => by
    rw [List.map_cons, agrees_cons] at ha
    rw [List.zipIdx_cons, List.map_cons] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ha.1
    · exact wf_axes xs (k + 1) ha.2 q hq

/-- The program of a model is sized, with the sizes of the model: every table that it computes is
sized. -/
theorem Model.sized_program (M : Model A N D K) {p : Program K}
    (h : Model.program dom M = some p) : p.sized (Model.size dom M) = true := by
  have ha := agrees_getD
    ((M.axes.map fun p ↦ (dom p.2).size) ++ Stmt.sizes dom M.body ++ Expr.sizes dom M.ret)
  rw [agrees_append, agrees_append, List.length_append, List.length_map, Nat.zero_add] at ha
  obtain ⟨⟨haxes, hbody⟩, hret⟩ := ha
  rw [Nat.zero_add] at hret
  simp only [Model.program, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨S, g⟩, hs, ⟨t, deps⟩, he, h⟩ := h
  dsimp only at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  obtain ⟨hS, hg, hn⟩ := Stmt.sized_steps (size := Model.size dom M) M.body _ ⟨M.axes.length, #[]⟩
    S g hs ⟨wf_axes M.axes 0 haxes, by simp, by simp⟩ hbody (by simp)
  have ht := Expr.sized_term (size := Model.size dom M) M.ret S g t deps he hS (hn ▸ hret) hg
  simp only [Program.sized, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun st hst ↦ hg st (Array.mem_def.2 hst), ht⟩

/-- Every table that the program of a model computes is sized, with the sizes of the model. -/
theorem Model.sized_tables [Semifield K] [LinearOrder K] (M : Model A N D K) {p : Program K}
    (h : Model.program dom M = some p) :
    ∀ x ∈ p.steps.foldl Step.run #[.const 1], x.Sized (Model.size dom M) :=
  Program.sized_tables (Model.sized_program M h)

end Memo
