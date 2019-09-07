module Test.Utils

%default total
%access export

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
