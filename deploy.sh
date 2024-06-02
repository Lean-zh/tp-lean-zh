#!/usr/bin/env bash
set -e

# Build
mdbook build
rm -rf out/.git

# 3. Deploy
rm -rf deploy
mkdir deploy
cd deploy
git init
cp -r ../out/./ .
git add -A
git commit -m "Update `date`"
git push https://github.com/Lean-zh/tp-lean-zh.git +HEAD:gh-pages
cd ..
rm -rf deploy
