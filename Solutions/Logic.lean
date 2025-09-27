section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro h
  intro hn
  apply hn h
  done

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hn
  by_cases lem : P
  case pos =>
    exact lem
  case neg =>
    have b := hn lem
    contradiction
  done

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  apply Iff.intro
  case mp =>
    exact doubleneg_elim P
  case mpr =>
    exact doubleneg_intro P
  done


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hor
  cases hor
  case inl h =>
    right
    exact h
  case inr h =>
    left
    exact h
  done

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro h
  apply And.intro
  case left =>
    exact h.right
  case right =>
    exact h.left
  done


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro h
  intro hp
  cases h
  case inl hl =>
    have b := hl hp
    contradiction
  case inr hr =>
    exact hr
  done



theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro h
  intro hp
  cases h
  case inl hl =>
    have b := hp hl
    contradiction
  case inr hr =>
    exact hr
  done


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro h
  intro hnq
  intro hp
  have q := h hp
  have b := hnq q
  contradiction
  done

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro h
  intro hp
  by_cases lem : Q
  case pos =>
    exact lem
  case neg =>
    have hnp := h lem
    have b := hnp hp
    contradiction
  done

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  apply Iff.intro
  case mp =>
    exact impl_as_contrapositive P Q
  case mpr =>
    exact impl_as_contrapositive_converse P Q
  done


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h
  by_cases lem : P
  case pos =>
    have hor : P ∨ ¬ P := by
      left
      exact lem
    have b := h hor
    contradiction
  case neg =>
    have hor : P ∨ ¬ P := by
      right
      exact lem
    have b := h hor
    contradiction
  done

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro h
  intro hn
  have pq : P → Q := by
    intro p
    have b := hn p
    contradiction
  have p := h pq
  have b := hn p
  contradiction
  done

------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases lem : P
  case pos =>
    right
    intro hq
    exact lem
  case neg =>
    left
    intro hp
    have b := lem hp
    contradiction
  done


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro hor
  intro hn
  rcases hn with ⟨hnp, hnq⟩
  cases hor
  case inl hl =>
    have b := hnp hl
    contradiction
  case inr hr =>
    have b := hnq hr
    contradiction
  done


theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro h
  intro hn
  cases hn
  case inl hl =>
    have b := hl h.left
    contradiction
  case inr hr =>
    have b := hr h.right
    contradiction
  done

------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro h
  by_cases lem : P
  case pos =>
    have pq : P ∨ Q := by
      left
      exact lem
    have b := h pq
    contradiction
  case neg =>
    by_cases lemq : Q
    case pos =>
      have qp : P ∨ Q := by
        right
        exact lemq
      have b := h qp
      contradiction
    case neg =>
      apply And.intro
      case right =>
        exact lemq
      case left =>
        exact lem
  done


theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro h
  intro hn
  cases hn
  case inl hl =>
    have b := h.left hl
    contradiction
  case inr hr =>
    have b := h.right hr
    contradiction
  done

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro h
  by_cases lemp : P
  case pos =>
    by_cases lemq : Q
    case pos =>
      have pq : P ∧ Q := by
        apply And.intro
        case left =>
          exact lemp
        case right =>
          exact lemq
      have b := h pq
      contradiction
    case neg =>
      left
      exact lemq
  case neg =>
    right
    exact lemp
  done


theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro h
  intro hn
  cases h
  case inl hl =>
    have b := hl hn.right
    contradiction
  case inr hr =>
    have b := hr hn.left
    contradiction
  done

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  apply Iff.intro
  case mp =>
    exact demorgan_conj P Q
  case mpr =>
    exact demorgan_conj_converse P Q
  done

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  apply Iff.intro
  case mp =>
    exact demorgan_disj P Q
  case mpr =>
    exact demorgan_disj_converse P Q
  done

------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h
  cases h.right
  case inl hl =>
    left
    apply And.intro
    case right =>
      exact hl
    case left =>
      exact h.left
  case inr hr =>
    right
    apply And.intro
    case right =>
      exact hr
    case left =>
      exact h.left
  done



theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro h
  apply And.intro
  case left =>
    cases h
    case inl hl =>
      exact hl.left
    case inr hr =>
      exact hr.left
  case right =>
    cases h
    case inl hl =>
      left
      exact hl.right
    case inr hr =>
      right
      exact hr.right
  done

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  apply And.intro
  case left =>
    cases h
    case inl hl =>
      left
      exact hl
    case inr hr =>
      right
      exact hr.left
  case right =>
    cases h
    case inl hl =>
      left
      exact hl
    case inr hr =>
      right
      exact hr.right
  done

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  cases h.left
  case inl hl =>
    left
    exact hl
  case inr hr =>
    cases h.right
    case inl hll =>
      left
      exact hll
    case inr hrr =>
      right
      apply And.intro
      case left =>
        exact hr
      case right =>
        exact hrr
  done

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h
  intro hp
  intro hq
  have or : P ∧ Q := by
    apply And.intro
    case left =>
      exact hp
    case right =>
      exact hq
  have b := h or
  exact b
  done

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro pqr
  intro and
  have qr := pqr and.left
  have r := qr and.right
  exact r
  done


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p
  done

------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro p
  left
  exact p
  done

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q
  right
  exact q
  done

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro pq
  exact pq.left
  done

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro pq
  exact pq.right
  done

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  apply Iff.intro
  case mp =>
    intro pp
    cases pp
    case inl hl =>
      exact hl
    case inr hr =>
      exact hr
  case mpr =>
    exact weaken_disj_right P P
  done

theorem conj_idem :
  (P ∧ P) ↔ P := by
  apply Iff.intro
  case mp =>
    exact weaken_conj_left P P
  case mpr =>
    intro p
    apply And.intro
    case left =>
      exact p
    case right =>
      exact p
  done

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro b
  contradiction
  done

theorem true_top :
  P → True  := by
  intro p
  trivial
  done

end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
