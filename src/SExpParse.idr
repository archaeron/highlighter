module SExpParse

import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Strings

%default total

||| A description of message formats. This gives the syntax of the
||| S-expressions that make up messages.
data MessageFmt =
	||| A particular keyword
	KWD String |
	||| Some data string
	STRING |
	||| Some data integer
	INT |
	||| Any number of repetitions of the same format
	MANY MessageFmt |
	||| A list, where each element has a specific format
	SEQ (List MessageFmt)


%name MessageFmt fmt, f

||| A singleton string. The type-level string forces the value-level
||| string to be the same. This is for readable pattern-matches and
||| for deriving serializers.
data Keyword : String -> Type where
  Kwd : (s : String) -> Keyword s

mutual
	||| A list of messages, elementwise based on a list of formats.
	|||
	||| This could also be `HList . map typeOf`, but it's a bit more
	||| clear this way.
	data MessageList : List MessageFmt -> Type where
		Nil : MessageList []
		(::) : (typeOf t) -> MessageList ts -> MessageList (t :: ts)

	||| The type of Idris data that represents a particular format.
	typeOf : MessageFmt -> Type
	typeOf (KWD name) = Keyword name
	typeOf STRING = String
	typeOf INT = Integer
	typeOf (MANY fmt) = List (typeOf fmt)
	typeOf (SEQ fmts) = MessageList fmts


--------------------------
-- Client to server
--------------------------
replCompletions : MessageFmt
replCompletions = SEQ [KWD "repl-completions", STRING]

loadFile : MessageFmt
loadFile = SEQ [KWD "load-file", STRING]

interpret : MessageFmt
interpret = SEQ [KWD "interpret", STRING]


||| A client message consists of some message along with a continuation
||| number
clientMsg : MessageFmt -> MessageFmt
clientMsg fmt = SEQ [fmt, INT]

--------------------------
-- Server to client
--------------------------

warning : MessageFmt
warning = SEQ [KWD "warning", STRING, INT, INT, STRING]

completionReturn : MessageFmt
completionReturn = MANY STRING

okMsg : MessageFmt -> MessageFmt
okMsg fmt = SEQ [KWD "ok", fmt]

--------------------------
-- Reading and writing
--------------------------

%default partial

||| Escape the characters in a string
escape : String -> String
escape str = concat (map escapeChar (unpack str))
	where
		escapeChar : Char -> String
		escapeChar '\\' = "\\\\"
		escapeChar '\"' = "\\\""
		escapeChar c = singleton c

||| Write data to an sexpr according to a message format specifier
serialize : (fmt : MessageFmt) -> (typeOf fmt) -> String
serialize (KWD name) (Kwd name) = ":" ++ name
serialize STRING str = "\"" ++ escape str ++ "\""
serialize INT i = show i
serialize (MANY fmt) xs = "(" ++ concat (intersperse " " (map (serialize fmt) xs)) ++ ")"
serialize (SEQ fmts) xs  = "(" ++ serializeList fmts xs ++ ")"
	where
		serializeList : (fs : List MessageFmt) -> MessageList fs -> String
		serializeList []  [] = ""
		serializeList (f::List.Nil) (x::MessageList.Nil) = serialize f x
		serializeList (f::fs) (x::xs) = serialize f x ++ " " ++ serializeList fs xs

||| Parse a backslash-escaped character
specialChar : Parser Char
specialChar = do
	c <- satisfy (const True)
	case c of
		'\"' => pure '\"'
		'\\' => pure '\\'
		ch   => pure ch

||| Parse the rest of a string, after the opening quote
strContents : Parser (List Char)
strContents =
	(char '\"' *!> pure [])
		<|> do
				c <- satisfy (/= '\"')
				if (c == '\\')
				then
					do
						c' <- specialChar
						rest <- strContents
						return (c' :: rest)
				else
					map (c ::) strContents

||| Parse a string
str : Parser String
str = char '\"' *!> map pack strContents <?> "String"

||| Parse parenthesized values
inParens : Parser a -> Parser a
inParens p = char '(' *!> p <*! char ')'

||| Derive a parser for some message format. It will extract the correct
||| type, as determined by `typeOf`.
parser : (fmt : MessageFmt) -> Parser (typeOf fmt)
parser (KWD x)	= string (":"++x) *!> pure (Kwd x)
parser STRING	 = str
parser INT		= integer
parser (MANY fmt) = inParens (parser fmt `sepBy` space)
parser (SEQ fmts) = inParens (parserForElts fmts)
	where
		parserForElts : (fmts : List MessageFmt) -> Parser (MessageList fmts)
		parserForElts []	  = pure []
		parserForElts (f::fs) = [| (parser f <*! space) :: (parserForElts fs) |]


----------------------------------------
-- Tests
----------------------------------------

testA : Either String (List String)
testA = parse (parser completionReturn) "(\"foo\" \"fonky\" \"founder\")"

-- The case block even checks my spelling!
covering
extractCompletionString : String -> Either String String
extractCompletionString str =
	case !(parse (parser replCompletions) str) of
		[Kwd "repl-completions", item] => return item


serializeCompletionCmd : String -> String
serializeCompletionCmd str = serialize replCompletions [Kwd "repl-completions", str]


-- should be Right foo
testSerializeParse : Either String String
testSerializeParse = extractCompletionString (serializeCompletionCmd "foo")


-- Local Variables:
-- idris-load-packages: ("lightyear")
-- idris-interpreter-flags: ("--typeintype")
-- End:
