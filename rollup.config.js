const resolve = require('@rollup/plugin-node-resolve');
const commonjs = require('@rollup/plugin-commonjs');
const babel = require('@rollup/plugin-babel');
const terser = require('@rollup/plugin-terser');
const pkg = require('./package.json');

const banner = `/**
 * PrimeOS JavaScript Library
 * Version: ${pkg.version}
 * A neural network-based operating system built on the Prime Framework
 * 
 * @license MIT
 */`;

const production = process.env.BUILD === 'production';

module.exports = [
  // UMD build (for browsers)
  {
    input: 'src/core.js',
    output: [
      {
        name: 'Prime',
        file: pkg.browser,
        format: 'umd',
        banner,
        sourcemap: !production,
        plugins: [production && terser()]
      }
    ],
    plugins: [
      resolve(),
      commonjs(),
      babel({
        babelHelpers: 'bundled',
        exclude: 'node_modules/**'
      })
    ]
  },
  
  // CommonJS and ES module builds (for Node.js and bundlers)
  {
    input: 'src/core.js',
    output: [
      { 
        file: pkg.main, 
        format: 'cjs',
        banner,
        sourcemap: !production,
        exports: 'named' 
      },
      { 
        file: pkg.module, 
        format: 'es',
        banner, 
        sourcemap: !production 
      }
    ],
    plugins: [
      babel({
        babelHelpers: 'bundled',
        exclude: 'node_modules/**'
      })
    ],
    external: Object.keys(pkg.dependencies || {})
  }
];