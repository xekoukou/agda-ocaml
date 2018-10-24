#!/bin/bash 

git clone https://github.com/projectatomic/bubblewrap
cd bubblewrap
./autogen.sh
make
sudo make install
