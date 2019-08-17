#!/bin/bash

mkdir -p $1/Haskell

cmd="ghc -j -O1 --make ./FixLits.hs"

echo $cmd

$cmd

echo "Fixing Literals"
for file in $(find $1 -maxdepth 1 -name "*.hs")
do
  baseval=`basename $file`
  if [[ $baseval != $2 && $baseval != $3 ]]
  then
    ./FixLits $file
    mv $file $1/Haskell
    echo "$file fixed."
  fi
done

echo "Adding missing imports"

unameOut="$(uname -s)"
case "${unameOut}" in
  Darwin*) SED=gsed;;
  *)       SED=sed
esac

for file in $(grep -l "CustomExtract" $1/Haskell/*.hs)
do
  grep -q "import qualified CustomExtract" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified CustomExtract\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.Char" $1/Haskell/*.hs)
do
  grep -q "import qualified Data\.Char" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.Char\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.Bits" $1/Haskell/*.hs)
do
  grep -q "import qualified Data\.Bits" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.Bits\nimport/}' $file
  fi
done

for file in $(grep -l "Data\.List" $1/Haskell/*.hs)
do
  grep -q "import qualified Data\.List" $file
  if [ $? -ne 0 ]
  then
    $SED -i -e '0,/^import/{s/^import/import qualified Data.List\nimport/}' $file
  fi
done

