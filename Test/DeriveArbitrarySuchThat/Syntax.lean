import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Attr

set_option guard_msgs.diff true

namespace Foo

inductive Bar where
| bar

inductive Baz : Bar → Prop where
| isBar : Baz .bar

end Foo

-- set_option trace.plausible.deriving.arbitrary true

#guard_msgs(drop info) in
derive_generator (∃ (b: Foo.Bar), Foo.Baz b)


section

open Foo

#guard_msgs(drop info) in
derive_generator (∃ (b: Bar), Baz b)


inductive Baz' : Bar → Bar → Prop where
| isBar2 : Baz' .bar .bar

/-- error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
---
error: Redundant alternative: Any expression matching
  _
will match one of the preceding alternatives
-/
#guard_msgs(error, drop info) in
derive_generator (fun a => ∃ b, Baz' a b)

end
