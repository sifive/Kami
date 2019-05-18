# How to use the Haskell Simulator

1. Make sure you have Haskell and GHC installed.  You will need the following package versions:
    - `base >=4.12 && <4.13`
    - `hashmap >=1.3 && <1.4`
    - `random >=1.1 && <1.2`
    - `bv >=0.5 && <0.6`
    - `vector >=0.12 && <0.13`
    - `text >=1.2 && <1.3`
    - `split >=0.2 && <0.3`
    - `hashable >=1.2 && <1.3`

2. In Coq, extract your module and everything else you want using the `Separate Extraction` command, extracting the following Kami terms as well:
    - `getFins`
    - `Fin.to_nat`
    - `fullFormatHex`
    - `fullFormatBinary`
    - `fullFormatDecimal`
    - `readReqName`
    - `readResName`
    - `readRegName`
    - `rfIsWrMask`
    - `rfNum`
    - `rfDataArray`
    - `rfRead`
    - `rfWrite`
    - `rfIdxNum`
    - `rfData`
    - `rfInit`
    - `pack`
    - `unpack`

See the file `Kami/Tutorial/ExtractEx.v` or `ProcKami/Instance.v` for examples.

3.  Create a file called `HaskellTarget.hs` which exports every module created by the extraction as well as everything you extracted.  See `RiscvSpecFormal/HaskellTarget.raw` for an example.

4.  Create another file with a module called `Main` which imports your `HaskellTarget` module along with `Simulator.All`.  
    1.   For every external method called in your module, write a function in Haskell of type `Val -> IO Val` which corresponds to how you would like this method to accept and return a value 
         (possibly with side-effects like changing state or logging messages).  Package the names of these methods with their Haskell implementations into an association list of type
         `[(String, Val -> IO Val)]`.
    2.  Provide a list of the names of the rules you would like to simulate in some privileged order (if you use the round robin scheduling, they will execute in this order).  To get a default
         list of rules from a module named `mod`, you can use the expression `map fst $ getRules mod`.
    3. The function needed to simulate a module is `simulate_module :: Int -> ([RuleT] -> Str (IO RuleT)) -> [String] -> [(String, Val -> IO Val)] -> [RegFileBase] -> BaseModule -> IO (Map String Val)`, defined in `Simulator/Simulator.hs`.
          - The first argument is a seed for a random number generator
          - The second argument is a function which provides a strategy for determining the next rule to execute
          - The third argument is a list of rule names, which should be supplied from ii)
          - The fourth argument is the association list of method implementations, which should be supplied from i)
          - The fifth argument is a list of register files, which should be extracted from Coq
          - The sixth argument is the module you wish to simulate, which should be extracted from Coq

         Write `main :: IO()`, invoking `simulate_module`.
    4.  Compile your `Main` module, making sure that GHC can find your `HaskellTarget.hs` as well as all the files in `Kami/Simulator`.
    5.   Supply the following arguments when applicable to run your executable:
            - `file_ident=file_path`, where `file_ident` is the name of a `RFFile` with `isArg=true` and `file_path` is the path to the hex file which this `RFFile` references
            - `file_path`, where `file_path` is the path to a hex file which an `RFFile` with `isArg=false` references
            - `pass:addr`, where addr is a hexadecimal value corresponding to a pass address
            - `fail:addr`, where addr is a hexadecimal value corresponding to a fail address

    See `Kami/SimulatorExample.hs` or `RiscvSpecFormal/Main.raw` for examples.
