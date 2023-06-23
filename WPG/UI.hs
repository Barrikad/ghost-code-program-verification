{-# LANGUAGE QuasiQuotes #-}
module WPG.UI where 

import WPG.Parse 
import WPG.Prog_lang
import WPG.Verify
import Text.RawString.QQ
import Text.Parsec
import Data.Either
import Data.SBV


prog1 = [r| 
[x,y,z]
g y := z
|]

prog2 = [r|
[]
g -| false;
|- exists x. exists y. exists z. x > 0 & y > 0 & z > 0 & x * x * x + y * y * y == z * z * z
|]

prog3 = [r|
[]
g -| x > 3;
|- x > 3
|]

prog4 = [r|
[y]
g -| y > 3;
|- x > 3
|]

prog5 = [r|
[]
g {
    {
        -| y >= 0
    }
    []
    {
        -| y < 0
    }
};
|- x > 0
|]

prog6 = [r|
[x,y,z]
g {
    var x;
    var y;
    var z;
    x := 3;
    y := 4;
    z := 5;
    |- x > 0 & y > 0 & z > 0 & x * x + y * y == z * z
};
|- exists x. exists y. exists z. x > 0 & y > 0 & z > 0 & x * x + y * y == z * z
|]

prog7 = [r|
[]
g {
{
    -| x > 0
} [] {
    |- true
}
};
|- x > 0
|]

check p =
    let pres = parse progParse "" p
        (gs,c) = either (error . ('\n':) . show) id pres in
    typeCheck gs Tru c

verify p = 
    let pres = parse progParse "" p
        (_,c) = either (error . ('\n':) . show) id pres in
    hoareTriple Tru c Tru

c = solver 
re = 
    satWithAll [] (existential ["x","y","z"] (\ x y z -> 
        3*3 + 4*4 .== (5*5 :: SInteger) .=>
        (x .> 0 .&& y .> 0 .&& z .> 0 .&& 
        x*x + y*y .== (z*z :: SInteger))))