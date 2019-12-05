# Dockerfile for binder
FROM sagemath/sagemath:8.7

RUN sage -pip install jupyterlab

# contents of repo to ${HOME}
COPY --chown=sage:sage . ${HOME}
