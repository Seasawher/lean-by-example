import Lean --#

/-! # 🎉タクティク

> 出典
> これは [Zulip のコメントで紹介されたタクティク](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.203.20or.204.3F/near/394490716) を拝借したものです．

Lean 言語はメタプログラミング機能が豊富で，タクティクも自分で作ることができます．ここでは例として，ゴールがすべて解決されたときにお祝いしてくれるタクティクを紹介します．
-/

open Lean Elab Tactic

elab "tada" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfo "Goals accomplished 🎉"
  else
    Term.reportUnsolvedGoals gs
    throwAbortTactic

example : True := by
  trivial
  tada
