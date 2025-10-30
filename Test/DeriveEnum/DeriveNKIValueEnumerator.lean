import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.DeriveEnum
import Test.DeriveArbitrary.DeriveNKIValueGenerator

deriving instance Enum for Value

set_option guard_msgs.diff true

-- Test that we can successfully synthesize instances of `Arbitrary` & `ArbitrarySized`

#guard_msgs(drop info, drop warning) in
#synth EnumSized Value

#guard_msgs(drop info, drop warning) in
#synth Enum Value

-- We test the command elaborator frontend in a separate namespace to
-- avoid overlapping typeclass instances for the same type
namespace CommandElaboratorTest

#guard_msgs(drop info, drop warning) in
derive_enum Value

end CommandElaboratorTest
