import Formal.Claude5O2StartC

/-! O2 model: starts in rhombus chart 4 (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

theorem st4_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)}
    (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) {P1 P2 : ℤ × ℤ}
    (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 ((0), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 P1)
    (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 P2) (hu1 : P1 - ((0), (0)) ∈ unitVec)
    (hp2 : P2 = ((0), (0)) + rotL (P1 - ((0), (0))) ∨ P2 = ((0), (0)) + rotR (P1 - ((0), (0))))
    (hd1 : Dom (t : ℤ) (d : ℤ) 4 P1) (hd2 : Dom (t : ℤ) (d : ℤ) 4 P2) : False := by
  obtain ⟨x1, y1⟩ := P1; obtain ⟨x2, y2⟩ := P2
  rw [unit_sub] at hu1; simp only [U2] at hu1
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hp2
  simp only [Dom, Hx, Rh] at hd1 hd2
  rcases hu1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (1) ∧ y1 = (0) ∧ x2 = (0) ∧ y2 = (1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb4_8 t d ht hd hp h0 h1 h2
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (0) ∧ y1 = (1) ∧ x2 = (1) ∧ y2 = (0) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb1_8 t d ht hd hp h0 h1 h2
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega

theorem st4_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)}
    (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) {P1 P2 : ℤ × ℤ}
    (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 ((0), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 P1)
    (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 P2) (hu1 : P1 - ((0), ((t : ℤ))) ∈ unitVec)
    (hp2 : P2 = ((0), ((t : ℤ))) + rotL (P1 - ((0), ((t : ℤ)))) ∨ P2 = ((0), ((t : ℤ))) + rotR (P1 - ((0), ((t : ℤ)))))
    (hd1 : Dom (t : ℤ) (d : ℤ) 4 P1) (hd2 : Dom (t : ℤ) (d : ℤ) 4 P2) : False := by
  obtain ⟨x1, y1⟩ := P1; obtain ⟨x2, y2⟩ := P2
  rw [unit_sub] at hu1; simp only [U2] at hu1
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hp2
  simp only [Dom, Hx, Rh] at hd1 hd2
  rcases hu1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (1) ∧ y1 = ((t : ℤ)) ∧ x2 = (1) ∧ y2 = ((t : ℤ) - 1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf9_1 t d ht hd hp h0 h1 h2
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (0) ∧ y1 = ((t : ℤ) - 1) ∧ x2 = (1) ∧ y2 = ((t : ℤ) - 1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf8_1 t d ht hd hp h0 h1 h2
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (1) ∧ y1 = ((t : ℤ) - 1) ∧ x2 = (1) ∧ y2 = ((t : ℤ)) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb4_2 t d ht hd hp h0 h1 h2
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = (1) ∧ y1 = ((t : ℤ) - 1) ∧ x2 = (0) ∧ y2 = ((t : ℤ) - 1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf4_7 t d ht hd hp h0 h1 h2

theorem st4_2 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)}
    (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) {P1 P2 : ℤ × ℤ}
    (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 (((t : ℤ)), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 P1)
    (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 P2) (hu1 : P1 - (((t : ℤ)), ((t : ℤ))) ∈ unitVec)
    (hp2 : P2 = (((t : ℤ)), ((t : ℤ))) + rotL (P1 - (((t : ℤ)), ((t : ℤ)))) ∨ P2 = (((t : ℤ)), ((t : ℤ))) + rotR (P1 - (((t : ℤ)), ((t : ℤ)))))
    (hd1 : Dom (t : ℤ) (d : ℤ) 4 P1) (hd2 : Dom (t : ℤ) (d : ℤ) 4 P2) : False := by
  obtain ⟨x1, y1⟩ := P1; obtain ⟨x2, y2⟩ := P2
  rw [unit_sub] at hu1; simp only [U2] at hu1
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hp2
  simp only [Dom, Hx, Rh] at hd1 hd2
  rcases hu1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ) - 1) ∧ y1 = ((t : ℤ)) ∧ x2 = ((t : ℤ)) ∧ y2 = ((t : ℤ) - 1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf1_1 t d ht hd hp h0 h1 h2
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ)) ∧ y1 = ((t : ℤ) - 1) ∧ x2 = ((t : ℤ) - 1) ∧ y2 = ((t : ℤ)) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf4_1 t d ht hd hp h0 h1 h2
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega

theorem st4_3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)}
    (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) {P1 P2 : ℤ × ℤ}
    (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 P1)
    (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 P2) (hu1 : P1 - (((t : ℤ)), (0)) ∈ unitVec)
    (hp2 : P2 = (((t : ℤ)), (0)) + rotL (P1 - (((t : ℤ)), (0))) ∨ P2 = (((t : ℤ)), (0)) + rotR (P1 - (((t : ℤ)), (0))))
    (hd1 : Dom (t : ℤ) (d : ℤ) 4 P1) (hd2 : Dom (t : ℤ) (d : ℤ) 4 P2) : False := by
  obtain ⟨x1, y1⟩ := P1; obtain ⟨x2, y2⟩ := P2
  rw [unit_sub] at hu1; simp only [U2] at hu1
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hp2
  simp only [Dom, Hx, Rh] at hd1 hd2
  rcases hu1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ)) ∧ y1 = (1) ∧ x2 = ((t : ℤ) - 1) ∧ y2 = (1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb9_2 t d ht hd hp h0 h1 h2
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ) - 1) ∧ y1 = (1) ∧ x2 = ((t : ℤ) - 1) ∧ y2 = (0) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kf1_7 t d ht hd hp h0 h1 h2
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ) - 1) ∧ y1 = (1) ∧ x2 = ((t : ℤ)) ∧ y2 = (1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb1_2 t d ht hd hp h0 h1 h2
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · obtain ⟨rfl, rfl, rfl, rfl⟩ : x1 = ((t : ℤ) - 1) ∧ y1 = (0) ∧ x2 = ((t : ℤ) - 1) ∧ y2 = (1) :=
        ⟨by omega, by omega, by omega, by omega⟩
      exact kb8_2 t d ht hd hp h0 h1 h2
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega
  · rcases hp2 with ⟨hc, he⟩ | ⟨hc, he⟩
    · exfalso; omega
    · exfalso; omega

end Claude5O2
