#!/bin/bash

g++ api_example.cpp -I../../../include -L../../../lib -lmathsat -lgmpxx -lgmp -lstdc++ -o api_example
