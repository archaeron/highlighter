module Main

import SExpParse
import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Strings

covering
main : IO ()
main =
	do
		putStr "> "
		line <- getLine
		case parse (parser (clientMsg interpret)) line of
			Left err =>
				putStrLn err *> main
			Right [[Kwd "interpret", cmd], i] =>
				do
					putStrLn "Calloo calleh, oh frabjous day! It worked!"
					putStrLn $ "Got command: " ++ cmd
					putStrLn $ "Continuation ID: " ++ show i
					main
