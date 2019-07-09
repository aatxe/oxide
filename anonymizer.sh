#!/bin/sh

git filter-branch --env-filter '
export GIT_AUTHOR_NAME="Anonymous Possum"
export GIT_AUTHOR_EMAIL="git@localhost"
' --tag-name-filter cat -- --branches --tags
