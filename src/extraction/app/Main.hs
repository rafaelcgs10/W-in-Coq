module Main where

import Infer
import Datatypes
import Parser
import Printing

main :: IO ()
main = do
    putStrLn "-- input example: \\x -> \\y -> \\z -> x (y z) --"
    s <- getLine
    let ast = runParser s
    case ast of
        Right ast' -> case runW ast' [] of
            (Left (t, _)) -> putStrLn $ show t
            (Right er) -> putStrLn $ show er
        Left erro -> putStrLn $ show erro 
