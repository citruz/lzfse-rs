#!/bin/sh

bindgen lzfse/src/lzfse.h \
  --no-layout-tests \
  --use-core \
  --allowlist-type='lzfse.*' \
  --allowlist-var='(?i)lzfse.*' \
  --allowlist-function='lzfse.*' > bindings.rs
