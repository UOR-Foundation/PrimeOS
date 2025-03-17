module.exports = {
  "env": {
    "browser": true,
    "node": true,
    "es2022": true,
    "jest": true
  },
  "extends": "eslint:recommended",
  "parserOptions": {
    "ecmaVersion": 2022,
    "sourceType": "module"
  },
  "rules": {
    "indent": [
      "error",
      2,
      { "SwitchCase": 1 }
    ],
    "linebreak-style": [
      "error",
      "unix"
    ],
    "quotes": [
      "error",
      "single",
      { "allowTemplateLiterals": true }
    ],
    "semi": [
      "error",
      "always"
    ],
    "no-console": [
      "warn",
      { "allow": ["warn", "error", "info"] }
    ],
    "no-unused-vars": [
      "warn",
      { "args": "none" }
    ],
    "strict": [
      "error",
      "function"
    ],
    "eqeqeq": [
      "error",
      "always"
    ],
    "no-var": "error",
    "prefer-const": "warn",
    "no-trailing-spaces": "error",
    "no-multiple-empty-lines": [
      "error",
      { "max": 2, "maxEOF": 1 }
    ]
  },
  "ignorePatterns": [
    "dist/*",
    "node_modules/*"
  ]
}