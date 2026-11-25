import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6658_731
    (search : let P := fun (x : Fin 14 → Bool) => ∃ i j : Fin 7, i ≠ 0 ∧
        (i = j ∨ i = j+1 ∨ i = j+3) ∧ x (Fin.castAdd 7 i) = true ∧ x (Fin.natAdd 7 j) = true
      let L := fun (x : Fin 14 → Bool) => ∃ j : Fin 7,
        (0 = j ∨ 0 = j+1 ∨ 0 = j+3) ∧ x (Fin.natAdd 7 j) = true
      let tests := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) (f : (Fin 14 → Bool) → Prop) =>
        ∀ x, (Minimal f x ∨ Maximal (fun y => ¬ f y) x) →
          ((C.wires (List.ofFn x)).getD w false = true ↔ f x)
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ 24 ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
        ∃ a b, a < 14+x1.size ∧ b < 14+x1.size ∧ tests x1 a P ∧ tests x1 b L)
    (extend : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) →
      ∀ (w : ℕ) (f : (Fin 14 → Bool) → Prop),
      (∀ x, (Minimal f x ∨ Maximal (fun y => ¬ f y) x) →
        ((x1.wires (List.ofFn x)).getD w false = true ↔ f x)) →
      ∀ x, ((x1.wires (List.ofFn x)).getD w false = true ↔ f x)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (24 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 < (14 : ℕ) + x1.size ∧ x3 < (14 : ℕ) + x1.size ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), ((x1.wires (List.ofFn x4)).getD x2 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ≠ (0 : Fin (7 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) ∧ ((x1.wires (List.ofFn x4)).getD x3 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)), ((0 : Fin (7 : ℕ)) = x5 ∨ (0 : Fin (7 : ℕ)) = x5 + (1 : Fin (7 : ℕ)) ∨ (0 : Fin (7 : ℕ)) = x5 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  obtain ⟨C, size, legal, a, b, ha, hb, pos, pencil⟩ := search
  exact ⟨C, size, legal, a, b, ha, hb, fun x => ⟨extend C legal a _ pos x, extend C legal b _ pencil x⟩⟩
