
from setuptools import setup, Extension
from Cython.Build import cythonize

# Define the extension module
ext_module = Extension(
    'my_extension', # Name of the module (used in import my_extension)
    sources=['my_extension.cpp'], # Source files for the extension
    extra_compile_args=['-std=c++17', '-Os'], # Add extra compiler flags if needed
    language='c++' # Specify C++ language
)

# Setup configuration
setup(
    name='my_extension', # Package name (can be different from module name)
    version='0.1',
    description='My C++ extension for chess move generation',
    ext_modules=[ext_module], # Include the extension module in the build
)

# setup(
#     name='Hello world app',
#     ext_modules=cythonize("helper.pyx"),
#     extra_compile_args=['-Os', '-s'],
# )