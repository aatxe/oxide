#!/bin/sh

git filter-branch --env-filter '
export GIT_AUTHOR_NAME="Anonymous Possum"
export GIT_AUTHOR_EMAIL="anon@example.com"
' --tag-name-filter cat -- --branches --tags
