# Docker file for TheoryMine

FROM ubuntu:14.04
MAINTAINER Lucas Dixon <lucas.dixon@gmail.com>

# Install the necessary base packages for Isabelle/TheoryMine theorem
# generation
RUN apt-get update && apt-get install -y \
  g++ \
  git \
  make \
  openjdk-6-jre \
  subversion \
  wget \
  nano

# Install additional packages for latex/certifictae/image generation
RUN apt-get install -y \
  imagemagick \
  curl \
  texlive-latex-extra \
  latex-cjk-all

# Install Isabelle-2015
RUN curl http://isabelle.in.tum.de/dist/Isabelle2015_linux.tar.gz \
  -o /usr/local/Isabelle2015_linux.tar.gz

RUN tar zxvf /usr/local/Isabelle2015_linux.tar.gz -C /usr/local/

# This is just a line to edit to make the below force to be re-run.
RUN echo "id:1"

# Install isaplib for Isabelle-2015
RUN git clone --branch Isabelle-2015 https://github.com/iislucas/isaplib.git \
    /usr/local/Isabelle2015/contrib/isaplib

# Copy the local directory as the IsaPlanner directory for Isabelle2009-2
COPY . /usr/local/Isabelle2015/contrib/IsaPlanner

RUN cd /usr/local/Isabelle2015/contrib/IsaPlanner && \
  /usr/local/Isabelle2015/bin/isabelle build -d . HOL-IsaPlannerSession && \
  /usr/local/Isabelle2015/bin/isabelle build -d . IsaPlanner-Test
