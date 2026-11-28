import OMAStatements.S_mo_488756

/-!
Source: https://mathoverflow.net/questions/488756
Credit: @Spinausore, assisted by Codex (gpt-6.2-sol).

Every subset of a fragmented set is fragmented: restrict the deletion sequence
to that subset. The comparisons required for a surviving vertex form a subset
of the original comparisons.
-/

namespace OMA.S_mo_488756

theorem fragmented_of_subset {α β : Type*} [DecidableEq α] [LE β]
    {w : α → α → β} {s t : Finset α} (hs : Fragmented w s) (ht : t ⊆ s) :
    Fragmented w t := by
  induction hs generalizing t with
  | empty =>
      have he : t = ∅ := Finset.subset_empty.mp ht
      subst t
      exact .empty
  | @delete s v hv rest ih =>
      by_cases hvt : v ∈ t
      · have hsub : t.erase v ⊆ s.erase v := by
          intro x hx
          obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hx
          exact Finset.mem_erase.mpr ⟨hne, ht hm⟩
        exact .delete
          ⟨hvt, fun x hx a ha b hb hab => hv.2 x (hsub hx) a (hsub ha) b (hsub hb) hab⟩
          (ih hsub)
      · apply ih
        intro x hx
        apply Finset.mem_erase.mpr
        exact ⟨fun e => hvt (e ▸ hx), ht hx⟩

end OMA.S_mo_488756

theorem OMA.solution : type_of% @OMA.S_mo_488756.main := by
  intro α β _ _ w _ s a hnot hfull
  exact hnot (OMA.S_mo_488756.fragmented_of_subset hfull (Finset.subset_insert a s))
