# Physlib

Physlib is an active project keeping track of theorems used to derive physical laws from basic assumptions within physics theories.

Currently, the project contains results in the following areas:
- [Newtonian Mechanics](https://github.com/cogrpar/Physlib/tree/main/Physlib/NewtonianMechanics)
    - [Kinematics](https://github.com/cogrpar/Physlib/blob/main/Physlib/NewtonianMechanics/KinematicsOneDimension.lean) - Shows that all trios of equations where one is the time derivative of the first and the other is the second time derivative of the first satisfy the kinematic equations.
    - [Reference Frames](https://github.com/cogrpar/Physlib/blob/main/Physlib/NewtonianMechanics/ReferenceFrames.lean) - Establishes a framework for thinking about 3 dimensional vectors as belonging to specific reference frames.  Shows that translating between frames corresponds to adding displacement, velocity, and acceleration vectors, and the idea of an inertial reference frame as one with zero relative acceleration to another.