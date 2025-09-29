import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.BinaryTree

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
#derive_checker (Between lo x hi)

#guard_msgs(drop info, drop warning) in
#derive_checker (BST lo hi t)
