'''
Created on Jul 17, 2013

@author: nvcleemp
'''
from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext

ext_modules = [Extension("conjecturing", ["conjecturing.pyx"])]

setup(
  name = 'Conjecturing module',
  cmdclass = {'build_ext': build_ext},
  ext_modules = ext_modules
)