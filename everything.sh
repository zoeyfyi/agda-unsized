#!/bin/bash

# Clear Everything.agda
echo "" > Everything.agda

# Write imports
for file in $(find $base_work_dir -name '*.agda')
do
  import="${file:2:-5}"
  import="${import//[\/]/\.}"
  if [ "$import" = "Everything" ]; then
    continue
  fi

  echo "import $import" >> Everything.agda
done

# Alphabetical sort
sort Everything.agda

echo "{-# OPTIONS --safe --without-K #-}
$(cat Everything.agda)" > Everything.agda