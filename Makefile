default:
	agda --ghc --ghc-dont-call-ghc example.agda
	stack run
