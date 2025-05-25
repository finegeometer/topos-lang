(cd agda-src && agda --compile Main.agda --compile-dir=../haskell-src --no-main --ghc-dont-call-ghc)
(cd haskell-src && ghc -outputdir ../target Main.hs -o ../Main)

