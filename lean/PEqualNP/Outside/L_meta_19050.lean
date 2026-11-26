import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19050

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mkGate (t : ℕ × ℕ × ℕ) : Gate :=
  match t.1 with
  | 0 => ⟨.and, [t.2.1, t.2.2]⟩
  | 1 => ⟨.or, [t.2.1, t.2.2]⟩
  | _ => ⟨.not, [t.2.1]⟩

def witness : Circuit :=
  ⟨([(0, 2, 5), (0, 6, 1), (1, 0, 4), (1, 2, 6), (2, 11, 11), (0, 10, 12), (1, 9, 13), (1, 8, 14)] : List (ℕ × ℕ × ℕ)).map mkGate, 15⟩

theorem fan : FanInTwo witness := by
  intro g hg
  obtain ⟨⟨k, a, b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases k with
  | zero => simp [mkGate]
  | succ k => cases k <;> simp [mkGate]

end PEqualNP.Outside.L_meta_19050

theorem PEqualNP.Outside.L_meta_19050 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4699 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19050.witness, PEqualNP.Outside.L_meta_19050.fan, by decide, ?_⟩
  decide +kernel
