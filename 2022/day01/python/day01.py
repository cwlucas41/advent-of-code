#! /usr/bin/env python3

import sys
from typing import List

def parse(filename: str) -> List[List[int]]:
    input = [[]]

    with open(filename) as file:
        for line in file.read().splitlines():
            if line == "":
                input.append([])
            else:
                input[-1].append(int(line))
    
    return input

def part_a() -> None:
    input = parse("../input.txt")

    max = 0

    elfIterator = 0
    while (elfIterator < len(input)):
        calories = 0
        itemIterator = 0
        while (itemIterator < len(input[elfIterator])):
            calories += input[elfIterator][itemIterator]
            itemIterator += 1

        if (calories > max):
            max = calories

        elfIterator += 1

    print(max)

def part_b(topN: int) -> None:
    input = parse("../input.txt")

    max = 0
    maxes = []

    elfIterator = 0
    while (elfIterator < len(input)):
        calories = 0
        itemIterator = 0
        while (itemIterator < len(input[elfIterator])):
            calories += input[elfIterator][itemIterator]
            itemIterator += 1
        
        if (len(maxes) < topN):
            maxes.append(calories)
        else:
            maxIterator = 0
            minIndex = 0
            while(maxIterator < len(maxes)):
                if (maxes[maxIterator] < maxes[minIndex]):
                    minIndex = maxIterator
                
                maxIterator += 1
            
            if (len(maxes) != 0 and maxes[minIndex] < calories):
                maxes[minIndex] = calories
        
        elfIterator += 1
        
    maxIterator = 0
    while (maxIterator < len(maxes)):
        max += maxes[maxIterator]
        maxIterator += 1
    
    print(max)

def main() -> int:
    part_a()
    part_b(3)

    return 0

if __name__ == '__main__':
    sys.exit(main())