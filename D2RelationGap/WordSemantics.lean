import D2RelationGap.Targets

/-! Soundness of free cancellation for the actual free group on OpenAI's generators.
Relator substitutions are sound under any group homomorphism respecting the four rules. -/
namespace D2RelationGap
open Targets

@[simp] theorem freeWord_nil : freeWord [] = 1 := rfl

@[simp] theorem freeWord_cons (l : Letter) (w : Word) :
    freeWord (l :: w) = freeLetter l * freeWord w := rfl

@[simp] theorem freeWord_append (u v : Word) :
    freeWord (u ++ v) = freeWord u * freeWord v := by
  simp [freeWord]

@[simp] theorem freeLetter_invert (l : Letter) :
    freeLetter (invert l) = (freeLetter l)⁻¹ := by
  rcases l with ⟨g, b⟩
  cases b <;> simp [freeLetter, invert]

theorem reducePush_sound (stack : Word) (l : Letter) :
    freeWord (reducePush stack l).reverse = freeWord stack.reverse * freeLetter l := by
  cases stack with
  | nil => simp [reducePush]
  | cons h t =>
    by_cases hc : (h == invert l) = true
    · have he : h = invert l := beq_iff_eq.mp hc
      subst h
      simp [reducePush, List.reverse_cons, mul_assoc]
    · simp [reducePush, hc, List.reverse_cons, mul_assoc]

theorem fold_reduce_sound (w stack : Word) :
    freeWord (w.foldl reducePush stack).reverse = freeWord stack.reverse * freeWord w := by
  induction w generalizing stack with
  | nil => simp
  | cons l w ih =>
    simp only [List.foldl_cons]
    rw [ih, reducePush_sound, freeWord_cons, mul_assoc]

theorem reduceWord_sound (w : Word) : freeWord (reduceWord w) = freeWord w := by
  simpa [reduceWord] using fold_reduce_sound w []

/-- Cancellation is preserved under every group homomorphism, in particular the maps to P and G. -/
theorem map_reduceWord_sound {H : Type*} [Group H] (f : F →* H) (w : Word) :
    f (freeWord (reduceWord w)) = f (freeWord w) := by
  rw [reduceWord_sound]

theorem freeWord_power (w : Word) (n : Nat) :
    freeWord (wordPower w n) = freeWord w ^ n := by
  rw [wordPower, reduceWord_sound]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ']

theorem freeWord_inverse (w : Word) : freeWord (inverseWord w) = (freeWord w)⁻¹ := by
  simp [inverseWord, freeWord, List.map_reverse, List.map_map, Function.comp_def,
    freeLetter_invert, List.prod_inv_reverse]

theorem substitute_sound {H : Type*} [Group H] (f : F →* H)
    (w lhs rhs : Word) (position : Nat)
    (hs : (w.drop position).take lhs.length = lhs)
    (he : f (freeWord lhs) = f (freeWord rhs)) :
    f (freeWord (reduceWord (w.take position ++ rhs ++ w.drop (position + lhs.length)))) =
      f (freeWord w) := by
  have hd : w.drop position = lhs ++ w.drop (position + lhs.length) := by
    calc
      w.drop position = (w.drop position).take lhs.length ++
          (w.drop position).drop lhs.length := (List.take_append_drop _ _).symm
      _ = _ := by simp [hs, List.drop_drop]
  have hw : w = w.take position ++ lhs ++ w.drop (position + lhs.length) := by
    calc
      w = w.take position ++ w.drop position := (List.take_append_drop _ _).symm
      _ = _ := by rw [hd, List.append_assoc]
  rw [reduceWord_sound]
  conv_rhs => rw [hw]
  simp only [freeWord_append, map_mul]
  rw [he]

theorem rewriteStep_sound {H : Type*} [Group H] (f : F →* H)
    (hrules : ∀ a b, (a, b) ∈ rules → f (freeWord a) = f (freeWord b))
    (w w' : Word) (s : RewriteStep) (success : rewriteStep w s = some w') :
    f (freeWord w') = f (freeWord w) := by
  cases hget : rules[s.rule]? with
  | none => simp [rewriteStep, hget] at success
  | some pair =>
    rcases pair with ⟨a, b⟩
    have hm : (a, b) ∈ rules := List.mem_of_getElem? hget
    have he : f (freeWord (wordPower a s.power)) = f (freeWord (wordPower b s.power)) := by
      simp only [freeWord_power, map_pow, hrules a b hm]
    by_cases hp : (s.power == 0) = true
    · simp [rewriteStep, hget, hp] at success
    · cases hrev : s.reverse <;> simp [rewriteStep, hget, hp, hrev] at success
      all_goals
        rcases success with ⟨hs, hout⟩
        rw [← hout]
        first
        | simpa only [List.append_assoc] using substitute_sound f w _ _ s.position hs he
        | simpa only [List.append_assoc] using substitute_sound f w _ _ s.position hs he.symm

theorem replay_sound {H : Type*} [Group H] (f : F →* H)
    (hrules : ∀ a b, (a, b) ∈ rules → f (freeWord a) = f (freeWord b))
    (steps : List RewriteStep) (w w' : Word) (success : replay w steps = some w') :
    f (freeWord w') = f (freeWord w) := by
  induction steps generalizing w w' with
  | nil =>
    simp only [replay, Option.some.injEq] at success
    subst w'
    exact map_reduceWord_sound f w
  | cons s steps ih =>
    cases hstep : rewriteStep (reduceWord w) s with
    | none => simp [replay, hstep] at success
    | some next =>
      simp only [replay, hstep, Option.bind_some] at success
      exact (ih next w' success).trans
        ((rewriteStep_sound f hrules _ _ s hstep).trans (map_reduceWord_sound f w))

theorem checkTrace_sound {H : Type*} [Group H] (f : F →* H)
    (hrules : ∀ a b, (a, b) ∈ rules → f (freeWord a) = f (freeWord b))
    (t : WordTrace) (accepted : checkTrace t = true) :
    f (freeWord t.start) = f (freeWord t.target) := by
  have hr : replay t.start t.steps = some (reduceWord t.target) :=
    beq_iff_eq.mp accepted
  exact (replay_sound f hrules _ _ _ hr).symm.trans (map_reduceWord_sound f t.target)

end D2RelationGap
